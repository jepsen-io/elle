(ns elle.anomalies
  "This protocol defines a unified way for different parts of Elle's analysis
  to report anomalies they may have encountered.")

(defprotocol Anomalies
  (anomalies [_] "Returns a map of keyword anomaly types to data
                 representations of those anomalies."))
