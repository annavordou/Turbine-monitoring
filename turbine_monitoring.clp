;; Name: Anna
;; Surname: Vordou
;; AEM: 3647


;; =========== Sensors ===========

;; define deftemplate for sensors' level
(deftemplate Level
    (slot name)
    (slot level))

;; define deftemplate fot solutions
(deftemplate Solution
   (slot message))

;; basic class "Sensor"
(defclass Sensor (is-a USER)
    (slot sensor-name (type SYMBOL) (visibility public))
    (slot sensor-value (type INTEGER) (visibility public))
    (slot sensor-type (type SYMBOL) (visibility public)))

;; constructor for sensors to find their value level and
;; print the proper message in symptoms
(defmessage-handler Sensor Sensor-create (?l ?h ?n1 ?n2)
    (bind ?sensor-level "Normal")
    (if (< ?self:sensor-value ?l)
        then
        (bind ?sensor-level "Low")
    else
        (if (> ?self:sensor-value ?h)
            then
            (bind ?sensor-level "High")
        else
            (if (and (>= ?self:sensor-value ?n1) (<= ?self:sensor-value ?n2))
                then
                (bind ?sensor-level "Normal")
            )
        )
    )
    (assert (Level (name ?self:sensor-name) (level ?sensor-level)))
    (printout t "-- " ?sensor-level " " ?self:sensor-type " in " ?self:sensor-name crlf)
)

;; subclass "DetectSensor" inheriting from "Sensor"
;; to represent fire & gas leak detectors
(defclass Detector (is-a Sensor)
    (slot sensor-value (type SYMBOL) (allowed-values on off) (visibility public)))

;; constructor for detectors to check their value
;; and print the proper message in symptoms
(defmessage-handler Detector Detector-create ()
    (if (and (eq ?self:sensor-name fire-sensor) (eq ?self:sensor-value on))
        then
        (printout t "-- FIRE IN THE PREMISES !!!" crlf))
    (if (and (eq ?self:sensor-name gas-leak-sensor) (eq ?self:sensor-value on))
        then
        (printout t "-- GAS LEAKAGE !!!" crlf))    
)


;; =========== Sensors' values per cycle ===========

;; initialize system to make sure rules run in the right order
(defrule initialize-system
  (declare (salience 1000))
  (not (initialized))
  =>
  (printout t "Initializing system..." crlf)
  (set-strategy depth)
  (set-dynamic-constraint-checking TRUE)
  (assert (initialized))
  (assert (current-cycle 1))
)

;; define deftemplate for sensors
(deftemplate Cycle
  (slot cycle)
  (slot T1)
  (slot T2)
  (slot P1)
  (slot P2)
  (slot fire-sensor)
  (slot rpm)
  (slot S1)
  (slot S2)
  (slot gas-leak-sensor))

;; define facts for sensors' values per cycle
(deffacts sensor-values
  (Cycle (cycle 1) (T1 300) (T2 500) (P1 4) (P2 5) (fire-sensor on) (rpm 7000) (S1 50) (S2 60) (gas-leak-sensor off))
  (Cycle (cycle 2) (T1 550) (T2 530) (P1 4) (P2 7) (fire-sensor off) (rpm 6000) (S1 50) (S2 75) (gas-leak-sensor on))
  (Cycle (cycle 3) (T1 200) (T2 400) (P1 1) (P2 9) (fire-sensor off) (rpm 900) (S1 35) (S2 55) (gas-leak-sensor off))
  (Cycle (cycle 4) (T1 200) (T2 580) (P1 6) (P2 9) (fire-sensor off) (rpm 9000) (S1 30) (S2 55) (gas-leak-sensor on))
  (Cycle (cycle 5) (T1 160) (T2 460) (P1 3) (P2 8) (fire-sensor on) (rpm 9500) (S1 85) (S2 90) (gas-leak-sensor off))
)

;; Update sensor values based on cycle
(defrule update-sensors
    ?now <- (current-cycle ?c)
    ?data <- (Cycle (cycle ?c)
                    (T1 ?t1)
                    (T2 ?t2)
                    (P1 ?p1)
                    (P2 ?p2)
                    (fire-sensor ?fire-sensor)
                    (rpm ?rpm)
                    (S1 ?s1)
                    (S2 ?s2)
                    (gas-leak-sensor ?gas-leak-sensor))
    =>
    (printout t crlf "Starting cycle " ?c crlf)
    (printout t "SYMPTOMS:" crlf)
    (send (make-instance t1 of Sensor (sensor-name T1) (sensor-value ?t1) (sensor-type temperature)) Sensor-create 100 500 0 600)
    (send (make-instance t2 of Sensor (sensor-name T2) (sensor-value ?t2) (sensor-type temperature)) Sensor-create 100 500 0 600)
    (send (make-instance p1 of Sensor (sensor-name P1) (sensor-value ?p1) (sensor-type pressure)) Sensor-create 2 8 0 10)
    (send (make-instance p2 of Sensor (sensor-name P2) (sensor-value ?p2) (sensor-type pressure)) Sensor-create 2 8 0 10)
    (send (make-instance fire of Detector (sensor-name fire-sensor) (sensor-value ?fire-sensor) (sensor-type fire)) Detector-create)
    (send (make-instance rpm of Sensor (sensor-name rpm) (sensor-value ?rpm) (sensor-type rotation)) Sensor-create 1000 8000 0 10000)
    (send (make-instance s1 of Sensor (sensor-name S1) (sensor-value ?s1) (sensor-type vibration)) Sensor-create 30 80 1 100)
    (send (make-instance s2 of Sensor (sensor-name S2) (sensor-value ?s2) (sensor-type vibration)) Sensor-create 30 80 1 100)
    (send (make-instance gas of Detector (sensor-name gas-leak-sensor) (sensor-value ?gas-leak-sensor) (sensor-type gas)) Detector-create)
    (printout t "SOLUTIONS:" crlf)
    (retract ?now)
    (retract ?data)
    (assert (current-cycle (+ ?c 1))) ; to move to the next cycle's values
)


;; =========== Rules for senosrs' levels ===========

(defrule PipeBlockage "Pipe blockage"
    (declare (salience 100))
    (Level (name P2) (level "High"))
    (Level (name T2) (level "High"))
    (or (Level (name rpm) (level "Normal")) (Level (name rpm) (level "Low")))
    =>
    (assert (Solution (message "Close main pipes and open backup pipes!")))
)

(defrule EngineOverloading "Engine overloading"
    (declare (salience 100))
    (Level (name P2) (level "High"))
    (Level (name T2) (level "High"))
    (Level (name rpm) (level "High"))
    =>
    (assert (Solution (message "Reduce fuel supply!")))
)

(defrule EngineUnderperforming "Engine underperforming"
    (declare (salience 100))
    (Level (name P2) (level "Low"))
    (Level (name rpm) (level "Low"))
    =>
    (assert (Solution (message "Increase fuel supply!")))
)

(defrule ProblemInInputPipes "Problem in input pipes"
    (declare (salience 100))
    (Level (name P1) (level "Low"))
    (Level (name T1) (level "Normal"))
    (Level (name T2) (level "Normal"))
    (Level (name S1) (level "Normal"))
    (Level (name S2) (level "Normal"))
    =>
    (assert (Solution (message "Start backup input system!")))
)

(defrule TurbineBladeIssue "Turbine blade issue"
    (declare (salience 100))
    (Level (name rpm) (level "High"))
    (Level (name S1) (level "High"))
    (Level (name S2) (level "High"))    
    =>
    (assert (Solution (message "Stop turbine operation!")))
)

(defrule TurbineCoolingIssue "Turbine cooling issue"
    (declare (salience 100))
    (Level (name T1) (level "High"))
    (Level (name T2) (level "High"))
    (Level (name P1) (level "Normal"))
    (Level (name P2) (level "Normal"))
    (Level (name rpm) (level "Normal"))
    =>
    (assert (Solution (message "Activate backup cooling system!")))
)

(defrule FireDetected "Fire detected"
    (declare (salience 100))
    (object (is-a Detector) (sensor-name fire-sensor) (sensor-value on))   
    =>
    (assert (Solution (message "Stop turbine operation!")))
)

(defrule GasLeakDetected "Gas leak detected"
    (declare (salience 100))
    (object (is-a Detector) (sensor-name gas-leak-sensor) (sensor-value on))  
    =>
    (assert (Solution (message "Stop turbine operation!")))
)


;; =========== Additional rules ===========

;; rule to print the solutions
(defrule PrintSolutions
    (declare (salience 10))
    ?solution <- (Solution (message ?message))
    =>
    (printout t ?message crlf)
    (retract ?solution))

;; rule to clear all Level facts at the end of the current cyrcle
(defrule ClearAllLevelFacts
    (declare (salience 1))
    (not (Solution))
    ?fact <- (Level (name ?x) (level ?y))
    =>
    (retract ?fact)
)

;; rule to clear all Sensor instances at the end of the current cyrcle
(defrule ClearAllInstances
    (declare (salience 1))
    (not (Solution))
    ?obj <- (object (is-a Sensor))
    =>
    (send ?obj delete)
)

;; rule to end the programm when there are no more senosors' values
;; also remove left garbage from working memory
(defrule TerminateProgram
    (not (Cycle))
    ?now <- (current-cycle ?c)
    =>
    (printout t crlf "There are no data for cycle 6! Ending program..." crlf)
    (retract ?now)
    (halt))