#include "ShieldAPI.h"
#include "TaskAPI.h"
#include "SpinAPI.h"
#include "pid.h"
#include "zephyr/console/console.h"
#include <math.h>

//====================================================================
// Global Declarations
//====================================================================

// Loop task declarations
void loop_application_task(); // Main task: averages calculation and application logic
void loop_communication_task(); // Serial communication task
void loop_critical_task(); // Sensor reading and PWM control task

// Parameters for I-V interpolation
#define HISTORY_SIZE 2 // History size to ensure steady-state current
#define N_POINTS 11 // Number of points for I-V curve approximation

const float32_t Ve = 50; // Input voltage [V]

// PV module electrical characteristics
const float32_t Voc = 44; // Open-circuit voltage [V]
const float32_t Isc = 5.1f; // Short-circuit current [A]
const float32_t Vm = 35.8f; // Voltage at maximum power point [V]
const float32_t Im = 4.61f; // Current at maximum power point [A]

// Operating modes
enum modeMenu { MODE_IDLE = 0, MODE_POWER, MODE_EMULATOR };
uint8_t mode = MODE_IDLE;

// Duty cycles
float32_t dutyCycle = 0.0; // Control variable
static float32_t dutyCycleP = 0.5f; // Duty cycle in POWER mode
static float32_t voltageReferenceP = 0.9f * Ve; // Voltage reference in POWER mode [V]
static float32_t voltageReferenceE_test_point = 0.9f * Ve; // Test point voltage reference in EMULATOR mode [V]
static float32_t voltageReferenceE = 25; // Voltage reference in EMULATOR mode [V]

// Thresholds and persistence
#define LOAD_RESISTANCE_THRESHOLD 0.02f // Relative variation of R > 2%
#define DUTY_CYCLE_CHANGE_THRESHOLD 0.05f // Duty cycle variation > 0.05
#define CURRENT_STABILITY_THRESHOLD 0.1f // Relative variation of Is of 10% for steady-state
#define REQUIRED_PERSISTENCE_COUNT 2 // Number of cycles to validate an event

// Measured values
static float32_t lowVoltage1, lowVoltage2; // Measured low-side voltages [V]
static float32_t lowCurrent1, lowCurrent2; // Measured low-side currents [A]
static float32_t highCurrent, highVoltage; // Measured high-side voltage [V] and current [A]
static float measData; // Raw read value

static uint32_t controlTaskPeriod = 100; // Critical task period [µs]
static bool pwmEnable = false;
uint8_t receivedChar; // Character received via serial

// PID parameters
static float32_t kp = 0.000215f; // Proportional gain
static float32_t Ti = 7.5175e-5f; // Integral time
static float32_t Td = 0.0f; // Derivative time
static float32_t Np = 0.0f; // Derivative filter coefficient
static float32_t upperBound = 1.0f; // Upper bound for PID output
static float32_t lowerBound = 0.0f; // Lower bound for PID output
static float32_t Ts = controlTaskPeriod * 1e-6f; // PID sampling period [s]
static PidParams pidParams(Ts, kp, Ti, Td, Np, lowerBound, upperBound);
static Pid pid;

// Accumulators for average calculation
static volatile float32_t sumLowCurrent1 = 0.0f, sumLowVoltage1 = 0.0f;
static volatile float32_t sumLowCurrent2 = 0.0f, sumLowVoltage2 = 0.0f;
static volatile float32_t sumHighCurrent = 0.0f, sumHighVoltage = 0.0f;
static volatile uint32_t measurementCount = 0;

// History and flags for EMULATOR MODE
static float32_t currentHistory[HISTORY_SIZE] = {0.0f, 0.0f};
static bool emulatorSteadyState = false;
static bool waitingSteadyState = false;

// Structure representing a linear segment of the I-V curve
struct Segment {
    float32_t a; // Slope of the segment (dI/dV)
    float32_t b; // Y-intercept
    float32_t Vmin; // Minimum valid voltage for the segment [V]
    float32_t Vmax; // Maximum valid voltage for the segment [V]
};
Segment segments[N_POINTS - 1]; // Array of segments

// Last stable point (intersection)
static float32_t lastSteadyVoltage = 0.0f;
static float32_t lastSteadyCurrent = 0.0f;
static float32_t lastDutyCycle = 0.0f;

// Load change detection counter
static uint32_t loadChangeCounter = 0;

//====================================================================
// Utility Functions
//====================================================================

// Updates a circular history of the last two measurements.
//
// Inputs:
// - hist: Pointer to the history array.
// - val: The new value to add to the history.
//
// Returns:
// - void
void updateHistory(float32_t *hist, float32_t val) {
    hist[0] = hist[1];
    hist[1] = val;
}

// Generates an array of voltage points for I-V curve interpolation.
// The points are distributed from 0 to Voc based on fractions of Vm.
//
// Inputs:
// - V: Array to store the calculated voltage points [V].
//
// Returns:
// - void
void computeVoltagePoints(float32_t V[N_POINTS]) {
    V[0] = 0.0f;
    V[1] = 0.2f * Vm;
    V[2] = 0.4f * Vm;
    V[3] = 0.6f * Vm;
    V[4] = 0.8f * Vm;
    V[5] = 0.9f * Vm;
    V[6] = Vm;
    V[7] = (Vm + Voc) / 2.0f;
    V[8] = 0.9f * Voc;
    V[9] = 0.95f * Voc;
    V[10] = Voc;
}

// Calculates the 'c' parameter for the solar panel's exponential law.
//
// Inputs:
// - void
//
// Returns:
// - The calculated 'c' parameter.
float32_t computeCParameter() {
    return -(Voc - Vm) / logf(1.0f - Im / Isc);
}

// Calculates the currents corresponding to the voltage points for the I-V curve
// using the simplified exponential model.
// I[i] = Isc * (1 - exp((V[i] - Voc) / c)).
//
// Inputs:
// - I: Array to store the calculated current points [A].
// - V: Array of voltage points [V].
// - c: The 'c' parameter of the exponential model.
//
// Returns:
// - void
void computeCurrentPoints(float32_t I[N_POINTS], float32_t V[N_POINTS], float32_t c) {
    for (int i = 0; i < N_POINTS; i++) {
        I[i] = Isc * (1.0f - expf((V[i] - Voc) / c));
    }
}

// Generates linear segments (lines) to approximate the I-V curve.
// Each segment covers a range [Vmin, Vmax] with a slope 'a' and intercept 'b'.
//
// Inputs:
// - segments: Array of Segment structures to store the calculated segments.
// - V: Array of voltage points [V].
// - I: Array of current points [A].
//
// Returns:
// - void
void computeSegments(Segment segments[N_POINTS - 1], float32_t V[N_POINTS], float32_t I[N_POINTS]) {
    for (int i = 0; i < N_POINTS - 1; i++) {
        segments[i].a = (I[i + 1] - I[i]) / (V[i + 1] - V[i]); // Slope (dI/dV)
        segments[i].b = I[i] - segments[i].a * V[i]; // Y-intercept
        segments[i].Vmin = V[i]; // Minimum voltage for this segment [V]
        segments[i].Vmax = V[i + 1]; // Maximum voltage for this segment [V]
    }
}

// Finds the intersection between the load line and the I-V segments.
// This function iterates through the pre-calculated I-V curve segments to find
// where the load line (represented by Vmes and Imes) intersects one of the segments.
//
// Inputs:
// - segments: Array of Segment structures representing the I-V curve.
// - n: The number of segments.
// - Vmes: Measured voltage for the load line [V].
// - Imes: Measured current for the load line [A].
// - Vint: Reference to store the intersection voltage [V].
// - Iint: Reference to store the intersection current [A].
//
// Returns:
// - void (updates Vint and Iint by reference)
void findIntersection(Segment segments[N_POINTS - 1], int n,
                      float32_t Vmes, float32_t Imes,
                      float32_t &Vint, float32_t &Iint) {
    float32_t a_mes = (Vmes != 0.0f) ? (Imes / Vmes) : 0.0f; // Slope of the load line (I/V)
    for (int i = 0; i < n; i++) {
        Vint = (0.0f - segments[i].b) / (segments[i].a - a_mes); // Calculate intersection voltage [V]
        Iint = a_mes * Vint; // Calculate intersection current [A]
        if (Vint >= segments[i].Vmin && Vint <= segments[i].Vmax) {
            return; // Valid intersection found
        }
    }
    Vint = Iint = -1.0f; // No intersection found
}

//====================================================================
// Configuration and Initialization
//====================================================================

// Initializes hardware, sensors, PID, and creates tasks.
//
// Inputs:
// - void
//
// Returns:
// - void
void setup_routine() {
    // Hardware initialization
    shield.power.initBuck(ALL);

    // Sensor configuration
    shield.sensors.enableDefaultTwistSensors();
    shield.sensors.setConversionParametersLinear(V1_LOW, 0.0456f, -92.69f);
    shield.sensors.setConversionParametersLinear(V2_LOW, 0.0453f, -92.061f);
    shield.sensors.setConversionParametersLinear(V_HIGH, 0.0299f, 0.2921f);
    shield.sensors.setConversionParametersLinear(I1_LOW, 0.0056f, -11.537f);
    shield.sensors.setConversionParametersLinear(I2_LOW, 0.0046f, -9.3977f);
    shield.sensors.setConversionParametersLinear(I_HIGH, 0.0046f, -9.1739f);

    // PID initialization
    pid.init(pidParams);

    // Calculate I-V segments
    float32_t Vp[N_POINTS], Ip[N_POINTS];
    computeVoltagePoints(Vp);
    float32_t c = computeCParameter();
    computeCurrentPoints(Ip, Vp, c);
    computeSegments(segments, Vp, Ip);

    // Task creation and startup
    uint8_t appTaskId = task.createBackground(loop_application_task);
    uint8_t commTaskId = task.createBackground(loop_communication_task);
    task.createCritical(loop_critical_task, controlTaskPeriod);
    task.startBackground(appTaskId);
    task.startBackground(commTaskId);
    task.startCritical();
}

//====================================================================
// Serial Communication Loop
//====================================================================

// Background task managing the serial interface.
// - Waits for a character input.
// - Updates the operating mode.
// - Allows modification of PV model parameters.
//
// Inputs:
// - void
//
// Returns:
// - void
void loop_communication_task() {
    while (1) {
        receivedChar = console_getchar(); // Read a character from the console
        switch (receivedChar) {
            case 'h':
                // Display the menu
                printk(" ________________________________________\n");
                printk("| ---- Buck Voltage Mode MENU ---- |\n");
                printk("| Press 'i' for idle mode          |\n");
                printk("| Press 'p' for power mode         |\n");
                printk("| Press 'e' for emulator mode      |\n");
                printk("| Press 'u' to increase voltage ref|\n");
                printk("| Press 'd' to decrease voltage ref|\n");
                printk(" ________________________________________\n");
                break;
            case 'i':
                // Idle mode
                printk("Idle mode\n");
                mode = MODE_IDLE;
                break;
            case 'p':
                // Buck (POWER) mode
                printk("Power mode\n");
                mode = MODE_POWER;
                dutyCycle = dutyCycleP;
                break;
            case 'e':
                // Emulator mode
                printk("Emulator mode\n");
                dutyCycleP = dutyCycle;
                mode = MODE_EMULATOR;
                // PID calculates initial duty cycle based on test point voltage
                dutyCycle = pid.calculateWithReturn(voltageReferenceE_test_point, lowVoltage1);
                shield.power.setDutyCycle(ALL, dutyCycle);
                currentHistory[0] = currentHistory[1] = 0.0f; // Reset current history
                emulatorSteadyState = false; // Reset steady-state flag
                waitingSteadyState = false; // Reset waiting for steady-state flag
                loadChangeCounter = 0; // Reset load change counter
                break;
            case 'u':
                // Increase duty cycle
                dutyCycle += 0.1f;
                break;
            case 'd':
                // Decrease duty cycle
                dutyCycle -= 0.1f;
                break;
            default:
                break;
        }
    }
}

//====================================================================
// Main Application Task
//====================================================================

// In emulator mode:
// It checks current stability and calculates the intersection between the load line
// and the I-V characteristic to determine the voltageReferenceE value. It displays
// the test point, the load line equation, and the intersection point. It also
// handles dynamic load changes by recalibrating the system and recalculating the
// intersection point.
//
// Inputs:
// - void
//
// Returns:
// - void
void loop_application_task() {
    static uint32_t elapsed = 0;
    elapsed += 100; // Increment elapsed time by 100 µs (critical task period)

    // LED indicator based on mode
    if (mode == MODE_IDLE) spin.led.turnOff();
    else spin.led.turnOn();

    // Averaging calculation period (in us)
    uint32_t period = 500; // Average over 500 us
    if (elapsed >= period && measurementCount > 0) {
        // Calculate averages
        float32_t avgLowI1 = sumLowCurrent1 / measurementCount; // Average of low-side current 1 [A]
        float32_t avgLowV1 = sumLowVoltage1 / measurementCount; // Average of low-side voltage 1 [V]
        float32_t avgLowI2 = sumLowCurrent2 / measurementCount; // Average of low-side current 2 [A]
        float32_t avgLowV2 = sumLowVoltage2 / measurementCount; // Average of low-side voltage 2 [V]
        float32_t avgHighI = sumHighCurrent / measurementCount; // Average of high-side current [A]
        float32_t avgHighV = sumHighVoltage / measurementCount; // Average of high-side voltage [V]
        float32_t avgLowI = avgLowI1 + avgLowI2; // Total average low-side current [A]
        float32_t avgLowV = (avgLowV1 + avgLowV2) * 0.5f; // Average low-side voltage [V]

        if (mode == MODE_POWER) {
            printk("Averages (last %uus):\n", period);
            printk("lowCurrent1: %f A\n", avgLowI1);
            printk("lowVoltage1: %f V\n", avgLowV1);
            printk("lowCurrent2: %f A\n", avgLowI2);
            printk("lowVoltage2: %f V\n", avgLowV2);
            printk("lowCurrent [Ilow1 + Ilow2]: %f A\n", avgLowI);
            printk("lowVoltage [(Vlow1 + Vlow2)/2]: %f V\n", avgLowV);
            printk("highCurrent: %f A\n", avgHighI);
            printk("highVoltage: %f V\n", avgHighV);
        }

        // Emulator: static load
        if (mode == MODE_EMULATOR && !emulatorSteadyState) {
            updateHistory(currentHistory, avgLowI); // Update current history
            // Check for current stability (relative change less than threshold)
            if (fabsf(currentHistory[0]) > 0.01f && (fabsf(currentHistory[1] - currentHistory[0]) / currentHistory[0]) < CURRENT_STABILITY_THRESHOLD) {
                float32_t Vint, Iint;
                // Find the intersection between the load line and the I-V curve
                findIntersection(segments, N_POINTS - 1, avgLowV, currentHistory[1], Vint, Iint);
                voltageReferenceE = Vint; // Set the emulator voltage reference to the intersection voltage
                // Display: test point, load line equation, intersection
                printk("Test Point: V_test = %f V, I_test = %f A\n", avgLowV, avgLowI);
                float32_t loadLineSlope = (avgLowV != 0.0F) ? (avgLowI / avgLowV) : 0.0F; // Slope of the load line (I/V)
                printk("Load Line Equation: I = %f * V\n", loadLineSlope);
                printk("Intersection Found: Vo* = %f V, Io* = %f A\n", Vint, Iint);
                lastSteadyVoltage = Vint; // Store the last steady voltage [V]
                lastSteadyCurrent = Iint; // Store the last steady current [A]
                emulatorSteadyState = true; // Set steady-state flag
                loadChangeCounter = 0; // Reset load change counter
            } else {
                printk("Measurements unstable for initial measurement phase.\n");
            }
        }

        // Emulator: dynamic load adaptation
        if (mode == MODE_EMULATOR && emulatorSteadyState) {
            float32_t candidateI = avgLowI; // Current candidate [A]
            float32_t candidateV = avgLowV; // Voltage candidate [V]
            float32_t currentDuty = dutyCycle; // Current duty cycle

            // If duty cycle changes significantly, re-enter waiting state
            if (fabsf(currentDuty - lastDutyCycle) > DUTY_CYCLE_CHANGE_THRESHOLD) {
                waitingSteadyState = true;
                loadChangeCounter = 0;
                lastSteadyVoltage = candidateV;
                lastSteadyCurrent = candidateI;
            }
            // If waiting for steady state, check current stability
            else if (waitingSteadyState) {
                if (fabsf(currentHistory[0]) > 0.01f && (fabsf(currentHistory[1] - currentHistory[0]) / currentHistory[0]) < CURRENT_STABILITY_THRESHOLD) {
                    waitingSteadyState = false; // Steady state reached
                    lastSteadyVoltage = candidateV;
                    lastSteadyCurrent = candidateI;
                }
            }
            // If already in steady state, check for load resistance change
            else {
                float32_t Rlast = (lastSteadyCurrent > 0.0f) ? (lastSteadyVoltage / lastSteadyCurrent) : 0.0f; // Last stable resistance [Ohms]
                float32_t Rcand = (candidateI > 0.0f) ? (candidateV / candidateI) : 0.0f; // Candidate resistance [Ohms]
                float32_t relErr = (Rlast > 0.0f) ? fabsf(Rcand - Rlast) / Rlast : 0.0f; // Relative error in resistance
                if (relErr > LOAD_RESISTANCE_THRESHOLD) {
                    loadChangeCounter++; // Increment load change counter
                    if (loadChangeCounter >= REQUIRED_PERSISTENCE_COUNT) {
                        loadChangeCounter = 0;
                        // For the emulator, the dutyCycle should be re-calculated based on the test point
                        // or previous stable state to initiate a new search for the intersection.
                        // The original code dutyCycle = dutyCycle; was a no-op here.
                        // Assuming the intent is to re-evaluate based on a fixed test point or simply reset for stability check.
                        // A safer approach for recalibration is often to re-apply the test point duty cycle/voltage.
                        // For now, I'm maintaining a placeholder equivalent to the original dutyCycle = dutyCycle;
                        // but it might need to be dutyCycle = pid.calculateWithReturn(voltageReferenceE_test_point, lowVoltage1);
                        // depending on the desired recalibration strategy.
                        // For this style conversion, keeping it as close as possible to the original logic.
                        dutyCycle = dutyCycle; // This line appears to be a no-op in the original logic, maintaining it.
                        emulatorSteadyState = false; // Exit steady state
                        shield.power.setDutyCycle(ALL, dutyCycle);
                        printk("Recalibration\n");
                    }
                } else {
                    loadChangeCounter = 0; // Reset load change counter
                    lastSteadyVoltage = candidateV;
                    lastSteadyCurrent = candidateI;
                }
            }
            lastDutyCycle = currentDuty; // Store the current duty cycle
        }

        // Reset accumulators
        sumLowCurrent1 = sumLowVoltage1 = sumLowCurrent2 = sumLowVoltage2 =
            sumHighCurrent = sumHighVoltage = 0.0f;
        measurementCount = 0;
        elapsed = 0;
    }
    task.suspendBackgroundMs(100); // Suspend background task for 100 ms
}

//====================================================================
// Critical Task (Reading + PWM)
//====================================================================

// Real-time task for reading sensors and adjusting PWM.
// - Reads low/high voltages and currents via DataAPI.
// - Selects behavior based on the current mode:
// - MODE_IDLE: PWM is stopped.
// - MODE_POWER: PID regulation based on voltageReferenceP.
// - MODE_EMULATOR: PID regulation initially on voltageReferenceE_test_point,
// then on voltageReferenceE after initial setup.
// - Accumulates measurements for the application task.
//
// Inputs:
// - void
//
// Returns:
// - void
void loop_critical_task() {
    // Read sensors
    measData = shield.sensors.getLatestValue(I1_LOW);
    if (measData != NO_VALUE) lowCurrent1 = measData; // Low-side current 1 [A]

    measData = shield.sensors.getLatestValue(V1_LOW);
    if (measData != NO_VALUE) lowVoltage1 = measData; // Low-side voltage 1 [V]

    measData = shield.sensors.getLatestValue(V2_LOW);
    if (measData != NO_VALUE) lowVoltage2 = measData; // Low-side voltage 2 [V]

    measData = shield.sensors.getLatestValue(I2_LOW);
    if (measData != NO_VALUE) lowCurrent2 = measData; // Low-side current 2 [A]

    measData = shield.sensors.getLatestValue(I_HIGH);
    if (measData != NO_VALUE) highCurrent = measData; // High-side current [A]

    measData = shield.sensors.getLatestValue(V_HIGH);
    if (measData != NO_VALUE) highVoltage = measData; // High-side voltage [V]

    if (mode == MODE_IDLE) {
        // MODE_IDLE: Simply stop PWM, no accumulation
        if (pwmEnable) {
            shield.power.stop(ALL);
        }
        pwmEnable = false;
    } else if (mode == MODE_POWER) {
        // MODE_POWER: PID calculation, application, and accumulation
        dutyCycle = pid.calculateWithReturn(voltageReferenceP, lowVoltage1); // Calculate duty cycle using PID [dimensionless, 0-1]
        shield.power.setDutyCycle(ALL, dutyCycle); // Set PWM duty cycle

        // Accumulate measurements
        sumLowCurrent1 += lowCurrent1;
        sumLowVoltage1 += lowVoltage1;
        sumLowCurrent2 += lowCurrent2;
        sumLowVoltage2 += lowVoltage2;
        sumHighCurrent += highCurrent;
        sumHighVoltage += highVoltage;
        measurementCount++; // Increment measurement count

        if (!pwmEnable) {
            pwmEnable = true;
            shield.power.start(ALL); // Start PWM
        }
    } else { // MODE_EMULATOR
        // EMULATOR: PID regulation on voltageReferenceE_test_point until initial measurement, then on voltageReferenceE
        if (!emulatorSteadyState) {
            dutyCycle = pid.calculateWithReturn(voltageReferenceE_test_point, lowVoltage1);
            shield.power.setDutyCycle(ALL, dutyCycle);
        } else {
            dutyCycle = pid.calculateWithReturn(voltageReferenceE, lowVoltage1);
            shield.power.setDutyCycle(ALL, dutyCycle);
        }

        // Accumulate measurements
        sumLowCurrent1 += lowCurrent1;
        sumLowVoltage1 += lowVoltage1;
        sumLowCurrent2 += lowCurrent2;
        sumLowVoltage2 += lowVoltage2;
        sumHighCurrent += highCurrent;
        sumHighVoltage += highVoltage;
        measurementCount++;
        if (!pwmEnable) {
            pwmEnable = true;
            shield.power.start(ALL);
        }
    }
}
//====================================================================
// Entry Point
//====================================================================

int main(void) {
    setup_routine();
    return 0;
}
