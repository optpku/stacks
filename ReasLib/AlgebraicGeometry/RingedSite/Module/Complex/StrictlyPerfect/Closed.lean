module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed duality for locally strictly perfect complexes on ringed sites

This leaf connects local strict perfectness to the canonical dual in a chosen closed structure.
The generic `MonoidalClosed.Dual` namespace owns the dual, comparison, evaluation, and
coevaluation; this file supplies the geometric invertibility criterion and its two pairing views.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite (ringedSiteModuleCategory)

noncomputable section

universe u v

namespace RingedSite.CochainComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C,
  (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

variable [MonoidalClosed
  (CochainComplex (RingedSite.ofCommRingSheaf J O).ModuleCat ℤ)]

#synth BraidedCategory
  (CochainComplex (RingedSite.ofCommRingSheaf J O).ModuleCat ℤ)

namespace IsLocallyStrictlyPerfect

/-- Local strict perfectness makes the canonical tensor-to-endomorphism comparison invertible. -/
@[stacks 0FPR "closed comparison criterion"]
theorem isIso_tensorIhomUnitToEnd
    {F : CochainComplex (RingedSite.ofCommRingSheaf J O).ModuleCat ℤ}
    (hF : IsLocallyStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) F) :
    IsIso (MonoidalClosed.tensorIhomUnitToEnd F) := sorry

/-- The canonical exact pairing exhibiting the closed dual as a right dual. -/
@[stacks 0FPR "canonical right exact pairing", reducible]
noncomputable def rightExactPairing
    {F : CochainComplex (RingedSite.ofCommRingSheaf J O).ModuleCat ℤ}
    [IsIso (MonoidalClosed.tensorIhomUnitToEnd F)] :
    ExactPairing F (MonoidalClosed.dual F) :=
  MonoidalClosed.Dual.exactPairing F

/-- Example 21.48.2 (0FPR): local strict perfectness supplies the canonical pairing as an
existence statement.  The concrete pairing datum is kept in `rightExactPairing`, whose explicit
`IsIso` input prevents a deferred proof from entering non-Prop data. -/
@[stacks 0FPR "canonical pairing existence"]
theorem rightExactPairing_nonempty
    {F : CochainComplex (RingedSite.ofCommRingSheaf J O).ModuleCat ℤ}
    (hF : IsLocallyStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) F) :
    Nonempty (ExactPairing F (MonoidalClosed.dual F)) := sorry

/-- The braided companion pairing exhibiting the closed dual as a left dual. -/
@[stacks 0FPR "braided left exact-pairing companion", reducible]
noncomputable def leftExactPairing
    {F : CochainComplex (RingedSite.ofCommRingSheaf J O).ModuleCat ℤ}
    [IsIso (MonoidalClosed.tensorIhomUnitToEnd F)] :
    ExactPairing (MonoidalClosed.dual F) F :=
  (rightExactPairing (F := F)).braidedSwap

/-- The canonical left pairing also exists for a locally strictly perfect complex. -/
@[stacks 0FPR "canonical left pairing existence"]
theorem leftExactPairing_nonempty
    {F : CochainComplex (RingedSite.ofCommRingSheaf J O).ModuleCat ℤ}
    (hF : IsLocallyStrictlyPerfect
      (X := RingedSite.ofCommRingSheaf J O) F) :
    Nonempty (ExactPairing (MonoidalClosed.dual F) F) := sorry

end IsLocallyStrictlyPerfect

end RingedSite.CochainComplex
