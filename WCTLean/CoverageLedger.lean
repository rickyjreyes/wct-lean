import Mathlib
import WCTLean.Registry

namespace WCTLean

/-!
# Machine-checked baseline and October promotion for issue #27

This is an explicitly curated equation-specific support set, NOT an automatic
theorem detector. The complementary list is computed from the canonical
registry and will fail the length checks if a curator changes either list
without updating the audited baseline. A promotion requires a substantive
equation-specific declaration and accompanying review/documentation.
-/

def equationSpecificIds : List EquationId :=
  [
  "M1", "M2", "M3", "M4", "M5", "M6A", "M6B", "M7", "E1A", "E1B",
  "E2", "E3", "E4", "E5", "E6", "E7", "E8", "E9", "E10", "E11",
  "E12", "E13", "E14", "E16", "E17", "E18", "E19", "E20", "E22", "E24",
  "E25", "E26", "E27", "E28", "E29", "E32", "E33", "E36", "E37", "E38",
  "E41", "E45", "E47", "E49", "E50", "E51", "E53", "E57", "E58", "E59",
  "E61", "E62", "E64", "E65", "E66", "E67", "E68", "E69", "E70", "E72",
  "E78", "E79", "E81", "E82", "CLE4", "CLE5", "CLE8", "CLE9", "CLE10", "G1", "EX", "EY",
  "EZ", "FA", "CM9", "CM11", "CM12", "CM13", "CM16", "TOP3", "TOP7", "CORR2"
  ]

def registryOnlyIds : List EquationId :=
  allEquationIds.filter (fun id => id ∉ equationSpecificIds)

theorem equationSpecificIds_length : equationSpecificIds.length = 82 := by
  native_decide

theorem equationSpecificIds_nodup : equationSpecificIds.Nodup := by
  native_decide

theorem equationSpecificIds_subset :
    ∀ id ∈ equationSpecificIds, id ∈ allEquationIds := by
  native_decide

theorem registryOnlyIds_length : registryOnlyIds.length = 60 := by
  native_decide

theorem registryOnlyIds_nodup : registryOnlyIds.Nodup := by
  native_decide

theorem registryOnlyIds_avoids_promoted :
    ∀ id ∈ registryOnlyIds, id ∉ equationSpecificIds := by
  native_decide

end WCTLean
