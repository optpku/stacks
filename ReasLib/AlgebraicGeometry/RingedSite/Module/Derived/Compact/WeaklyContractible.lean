module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Compact.Absolute
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology.WeaklyContractible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compactness of generators over weakly contractible objects

This is the source-facing specialization of the finite-dimension compactness criterion.  The
cohomological hypotheses are supplied by the independent weak-contractibility bridges.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived.LocalizedGenerator

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [IsGrothendieckAbelian.{w} (RingedSite.ModuleCat.{w} X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [HasSheafify X.siteTopology AddCommGrpCat.{w}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat.{w})]

/-- Lemma 21.52.6 (094E): a quasi-compact weakly contractible object has a compact degree-zero
localized generator. -/
@[stacks 094E]
theorem isCompactObject_of_quasiCompact_weaklyContractible
    (U : X) (hUqc : X.siteTopology.QuasiCompactObject U)
    [X.siteTopology.IsWeaklyContractible U]
    [(SheafOfModules.Localization.restriction X.structureSheaf U :
      RingedSite.ModuleCat.{w} X ⥤
        SheafOfModules.{w} (X.structureSheaf.over U)).IsRightAdjoint] :
    IsCompactObject (localizedGenerator X U) := sorry

end RingedSite.Hom.ModuleDerived.LocalizedGenerator

end
