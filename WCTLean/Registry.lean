import Mathlib

namespace WCTLean

/-!
# Canonical WCT equation registry

Every object in the corrected 142-object WCT registry receives a compiled
identifier and an effective symbolic-audit status. Registration is not a proof
of the equation's analytical or physical content.
-/

abbrev EquationId := String

inductive EquationFamily where
  | master
  | canonical
  | electron
  | auxiliary
  | cosmology
  | topology
  | correction
  deriving DecidableEq, Repr, BEq

inductive AuditStatus where
  | pass
  | conditional
  | definition
  | openClaim
  deriving DecidableEq, Repr, BEq

def numberedIds (prefix : String) (start count : Nat) : List EquationId :=
  (List.range count).map fun offset => prefix ++ toString (start + offset)

def masterIds : List EquationId :=
  ["M1", "M2", "M3", "M4", "M5", "M6A", "M6B", "M7", "M8"]

def canonicalIds : List EquationId :=
  ["E1A", "E1B"] ++ numberedIds "E" 2 81

def electronIds : List EquationId := numberedIds "CLE" 1 10

def auxiliaryIds : List EquationId := ["G1", "EX", "EY", "EZ", "FA"]

def cosmologyIds : List EquationId := numberedIds "CM" 1 20

def topologyIds : List EquationId := numberedIds "TOP" 1 9

def correctionIds : List EquationId := numberedIds "CORR" 1 6

def allEquationIds : List EquationId :=
  masterIds ++ canonicalIds ++ electronIds ++ auxiliaryIds ++
    cosmologyIds ++ topologyIds ++ correctionIds

def passIds : List EquationId := ["M2", "M3", "M4", "M7", "E1A", "E1B", "E2", "E3", "E4", "E5", "E6", "E7", "E8", "E9", "E10", "E11", "E12", "E13", "E14", "E16", "E17", "E18", "E20", "E21", "E24", "E26", "E28", "E29", "E30", "E33", "E37", "E38", "E45", "E47", "E49", "E51", "E53", "E57", "E58", "E59", "E61", "E62", "E64", "E65", "E67", "E69", "E81", "CLE2", "CLE4", "CLE6", "CLE7", "CLE9", "CLE10", "G1", "EX", "EY", "EZ", "CM9", "CM11"]

def conditionalIds : List EquationId := ["M1", "M5", "E15", "E19", "E22", "E23", "E31", "E32", "E40", "E41", "E48", "E50", "E54", "E56", "E66", "E68", "E70", "E71", "E72", "E76", "E80", "CLE5", "CLE8", "FA", "TOP3", "TOP7", "CORR2"]

def definitionIds : List EquationId := ["M6A", "E25", "E27", "E35", "E36", "E39", "E44", "E52", "E55", "E60", "E63", "E73", "E79", "E82", "CLE1", "CLE3", "CM12", "CM13", "CM16", "CM18", "TOP1", "TOP2", "TOP5", "CORR1", "CORR3", "CORR4"]

def openIds : List EquationId := ["M6B", "M8", "E34", "E42", "E43", "E46", "E74", "E75", "E77", "E78", "CM1", "CM2", "CM3", "CM4", "CM5", "CM6", "CM7", "CM8", "CM10", "CM14", "CM15", "CM17", "CM19", "CM20", "TOP4", "TOP6", "TOP8", "TOP9", "CORR5", "CORR6"]

def statusPartition : List EquationId :=
  passIds ++ conditionalIds ++ definitionIds ++ openIds

def effectiveStatus? (id : EquationId) : Option AuditStatus :=
  if id ∈ passIds then some .pass
  else if id ∈ conditionalIds then some .conditional
  else if id ∈ definitionIds then some .definition
  else if id ∈ openIds then some .openClaim
  else none

def equationFamily? (id : EquationId) : Option EquationFamily :=
  if id ∈ masterIds then some .master
  else if id ∈ canonicalIds then some .canonical
  else if id ∈ electronIds then some .electron
  else if id ∈ auxiliaryIds then some .auxiliary
  else if id ∈ cosmologyIds then some .cosmology
  else if id ∈ topologyIds then some .topology
  else if id ∈ correctionIds then some .correction
  else none

structure CanonicalEntry where
  id : EquationId
  family : EquationFamily
  status : AuditStatus
  deriving Repr

def canonicalRegistry : List CanonicalEntry :=
  allEquationIds.filterMap fun id =>
    match equationFamily? id, effectiveStatus? id with
    | some family, some status => some { id := id, family := family, status := status }
    | _, _ => none

theorem masterIds_length : masterIds.length = 9 := by native_decide
theorem canonicalIds_length : canonicalIds.length = 83 := by native_decide
theorem electronIds_length : electronIds.length = 10 := by native_decide
theorem auxiliaryIds_length : auxiliaryIds.length = 5 := by native_decide
theorem cosmologyIds_length : cosmologyIds.length = 20 := by native_decide
theorem topologyIds_length : topologyIds.length = 9 := by native_decide
theorem correctionIds_length : correctionIds.length = 6 := by native_decide

theorem allEquationIds_length : allEquationIds.length = 142 := by native_decide
theorem allEquationIds_nodup : allEquationIds.Nodup := by native_decide

theorem passIds_length : passIds.length = 59 := by native_decide
theorem conditionalIds_length : conditionalIds.length = 27 := by native_decide
theorem definitionIds_length : definitionIds.length = 26 := by native_decide
theorem openIds_length : openIds.length = 30 := by native_decide

theorem statusPartition_length : statusPartition.length = 142 := by native_decide
theorem statusPartition_nodup : statusPartition.Nodup := by native_decide

theorem statusPartition_complete :
    statusPartition.toFinset = allEquationIds.toFinset := by
  native_decide

theorem every_registered_id_has_status :
    ∀ id ∈ allEquationIds, (effectiveStatus? id).isSome := by
  native_decide

theorem every_registered_id_has_family :
    ∀ id ∈ allEquationIds, (equationFamily? id).isSome := by
  native_decide

theorem canonicalRegistry_length : canonicalRegistry.length = 142 := by
  native_decide

end WCTLean
