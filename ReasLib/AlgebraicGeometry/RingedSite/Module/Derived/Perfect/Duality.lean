/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Duality
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality.HomotopyColimit
public import ReasLib.CategoryTheory.Monoidal.Invertible
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Duality of perfect derived module sheaves

This leaf connects perfectness for the canonical K-flat tensor product to the generic
closed-monoidal duality API.  Comparison morphisms remain the generic canonical data; only their
invertibility and the geometric perfectness statements are specialized here.
-/

open CategoryTheory

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf J CommRingCat.{w})
variable [∀ U : RingedSite.ofCommRingSheaf J O,
  HasWeakSheafify
    ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : RingedSite.ofCommRingSheaf J O,
  ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology.WEqualsLocallyBijective
    AddCommGrpCat.{w}]
variable [KFlat.HomotopyTensorDescends O] [KFlat.TensorDescends O]
variable [KFlat.IsLocalization O]
variable [MonoidalClosed (ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O))]

namespace IsPerfect

/-- Lemma 21.48.4 (1): the closed-monoidal dual of a perfect derived module sheaf is perfect. -/
@[stacks 08JJ "(1)"]
theorem dual
    {K : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hK : K.IsPerfect) :
    (MonoidalClosed.dual K).IsPerfect := sorry

/-- Perfectness makes the canonical tensor-to-endomorphism comparison invertible. -/
@[stacks 0FPU "canonical pairing criterion"]
theorem isIso_tensorIhomUnitToEnd
    {K : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hK : K.IsPerfect) :
    IsIso (MonoidalClosed.tensorIhomUnitToEnd K) := sorry

/-- Lemma 21.48.4 (2): the canonical bidual comparison of a perfect derived module sheaf is
invertible. -/
@[stacks 08JJ "(2)"]
theorem isIso_bidualComparison
    {K : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hK : K.IsPerfect) :
    IsIso (MonoidalClosed.Dual.bidualComparison K) := sorry

/-- Lemma 21.48.4 (3): for a perfect source, the canonical tensor/internal-Hom comparison is
invertible at every target. -/
@[stacks 08JJ "(3)"]
theorem isIso_tensorComparison
    {K M : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hK : K.IsPerfect) :
    IsIso (MonoidalClosed.Dual.tensorComparison K M) := sorry

/-- Lemma 21.48.4 (4): the degree-zero comparison from tensoring with the dual to morphisms out
of a perfect object is bijective. -/
@[stacks 08JJ "(4)"]
theorem homComparison_bijective
    {K M : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hK : K.IsPerfect) :
    Function.Bijective (MonoidalClosed.Dual.homComparison K M) := sorry

/-- Lemma 21.48.7 (1): explicit pairing data
`ExactPairing M N` for the canonical derived tensor product imply that `M` is perfect. -/
@[stacks 0FPV "(1)"]
theorem ofExactPairing
    {M N : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (p : ExactPairing M N) :
    M.IsPerfect := sorry

/-- Lemma 21.49.2 (2): a tensor-invertible derived module sheaf is perfect. -/
@[stacks 0FPY "(2)"]
theorem of_isInvertible
    {M : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hM : MonoidalCategory.isInvertibleObject M) :
    M.IsPerfect := sorry

/-- Lemma 21.48.8 (0A0A): if `Khocolim` is a sequential homotopy colimit of
perfect derived module sheaves `K.obj n`, then internal Hom from `Khocolim` into `E` is the
homotopy limit of the canonical inverse system `n ↦ E ⊗ MonoidalClosed.dual (K.obj n)`. -/
@[stacks 0A0A]
theorem homotopyLimit_dualTensor_of_homotopyColimit
    {K : ℕ ⥤ ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    {Khocolim : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)}
    (hK : HomotopyColimit.IsOf K Khocolim)
    (hperfect : ∀ n, (K.obj n).IsPerfect)
    (E : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)) :
    HomotopyLimit.IsOf (MonoidalClosed.Dual.tensorTower K E)
      ((ihom Khocolim).obj E) := sorry

end IsPerfect

end RingedSite.Hom.ModuleDerived
