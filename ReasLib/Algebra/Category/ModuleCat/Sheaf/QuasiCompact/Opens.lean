module

public import Mathlib.Topology.Sheaves.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.QuasiCompact
public import ReasLib.Topology.Opens.QuasiCompact

/-!
# Sections of module sheaves over compact opens

Import surface combining the site-theoretic quasi-compact evaluation API
(`SheafOfModules.Evaluation.sigmaComparison_isIso_of_quasiCompact`) with the bridge
`TopologicalSpace.Opens.quasiCompactObject_of_isCompact`, which turns `IsCompact U` into the
`QuasiCompactObject` hypothesis on the site of opens.  The generic site declarations remain the
sole theorem owners.
-/

@[expose] public section
