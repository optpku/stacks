/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality
public import ReasLib.CategoryTheory.Monoidal.Closed.TensorInternalHom
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Closed-monoidal duality for derived module sheaves

This leaf owns the ringed-site specialization of the generic closed-monoidal dual and its
evaluation maps.  Chapter 21 entries only recall these declarations; downstream developments can
import this file without depending on a chapter facade.
-/

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

local notation "D" => RingedSiteDerived J 𝒪
set_option quotPrecheck false in
local notation:20 A " ⟹ " B:19 => (ihom A).obj B

/-- The derived closed-monoidal dual `L^∨ = ihom L (𝟙_ D)`. -/
@[stacks 08JE "derived closed-monoidal dual"]
abbrev ringedSiteDerivedDualObject (L : D) : D :=
  (ihom L).obj (𝟙_ D)

/-- The source-facing notation for `ringedSiteDerivedDualObject`. -/
notation:max L:max "^∨" => ringedSiteDerivedDualObject L

/-- The canonical comparison `M ⊗ L^∨ ⟶ ihom L M`. -/
@[stacks 08JE "derived tensor/internal-Hom comparison"]
abbrev ringedSiteDerivedEvaluationHom (L M : D) :
    M ⊗ L^∨ ⟶ L ⟹ M :=
  MonoidalClosed.tensorInternalHomComparison M (𝟙_ D) L ≫
    (ihom L).map (ρ_ M).hom

/-- The uncurried form of `ringedSiteDerivedEvaluationHom`. -/
@[stacks 08JE "derived tensor/internal-Hom comparison specification"]
theorem ringedSiteDerivedEvaluationHom_uncurry (L M : D) :
    uncurry (ringedSiteDerivedEvaluationHom L M) =
      (α_ L M L^∨).inv ≫
        (β_ L M).hom ▷ L^∨ ≫
        (α_ M L L^∨).hom ≫
        M ◁ (ihom.ev L).app (𝟙_ D) ≫
        (ρ_ M).hom := sorry

/-- The dual evaluation `L^∨ ⊗ L ⟶ 𝟭_ D`. -/
@[stacks 08JE "derived dual evaluation"]
abbrev ringedSiteDerivedDualEvaluation (L : D) :
    L^∨ ⊗ L ⟶ 𝟙_ D :=
  (β_ L^∨ L).hom ≫ (ihom.ev L).app (𝟙_ D)

/-- The braided closed-monoidal specification of the derived dual evaluation. -/
@[stacks 08JE "derived dual evaluation specification"]
theorem ringedSiteDerivedDualEvaluation_eq_braided_uncurry (L : D) :
    ringedSiteDerivedDualEvaluation L =
      (β_ L^∨ L).hom ≫ MonoidalClosed.uncurry (𝟙 L^∨) := sorry

/-- The degree-zero comparison sends `𝟙_ D ⟶ M ⊗ L^∨` to `L ⟶ M`. -/
@[stacks 08JD "derived degree-zero dual comparison"]
noncomputable abbrev ringedSiteDerivedEvaluationH0ToHom (L M : D) :
    (𝟙_ D ⟶ M ⊗ L^∨) → (L ⟶ M) :=
  fun s ↦ MonoidalClosed.uncurry' (s ≫ ringedSiteDerivedEvaluationHom L M)

/-- Currying the degree-zero comparison recovers postcomposition with evaluation. -/
@[simp, stacks 08JD "derived degree-zero dual comparison specification"]
theorem curry'_ringedSiteDerivedEvaluationH0ToHom
    (L M : D) (s : 𝟙_ D ⟶ M ⊗ L^∨) :
    MonoidalClosed.curry' (ringedSiteDerivedEvaluationH0ToHom L M s) =
      s ≫ ringedSiteDerivedEvaluationHom L M := sorry

/-- Naturality of the degree-zero comparison in the target variable. -/
@[stacks 08JD "derived degree-zero dual comparison naturality"]
theorem ringedSiteDerivedEvaluationH0ToHom_natural
    {L M₁ M₂ : D} (f : M₁ ⟶ M₂)
    (s : 𝟙_ D ⟶ M₁ ⊗ L^∨) :
    ringedSiteDerivedEvaluationH0ToHom L M₂
        (s ≫ (f ⊗ₘ 𝟙 (L^∨))) =
      ringedSiteDerivedEvaluationH0ToHom L M₁ s ≫ f := sorry

section Additive

/-- Additivity of the degree-zero comparison in the global-sections variable. -/
@[stacks 08JD "additivity of the derived degree-zero dual comparison"]
theorem ringedSiteDerivedEvaluationH0ToHom_add
    [Preadditive D] [MonoidalPreadditive D]
    (L M : D) (s t : 𝟙_ D ⟶ M ⊗ L^∨) :
    ringedSiteDerivedEvaluationH0ToHom L M (s + t) =
      ringedSiteDerivedEvaluationH0ToHom L M s +
        ringedSiteDerivedEvaluationH0ToHom L M t := sorry

/-- The additive-homomorphism view of the degree-zero comparison. -/
@[stacks 08JD "additive derived degree-zero dual comparison"]
noncomputable abbrev ringedSiteDerivedEvaluationH0ToHomAddMonoidHom
    [Preadditive D] [MonoidalPreadditive D]
    (L M : D) :
    AddMonoidHom (𝟙_ D ⟶ M ⊗ L^∨) (L ⟶ M) :=
  AddMonoidHom.mk'
    (ringedSiteDerivedEvaluationH0ToHom L M)
    (ringedSiteDerivedEvaluationH0ToHom_add L M)

/-- The `AddCommGrpCat` morphism underlying the degree-zero comparison. -/
@[stacks 08JD "AddCommGrp-valued derived degree-zero dual comparison"]
noncomputable abbrev ringedSiteDerivedEvaluationH0ToHomAddCommGrpHom
    [Preadditive D] [MonoidalPreadditive D]
    (L M : D) :
    AddCommGrpCat.of (𝟙_ D ⟶ M ⊗ L^∨) ⟶
      AddCommGrpCat.of (L ⟶ M) :=
  AddCommGrpCat.ofHom (ringedSiteDerivedEvaluationH0ToHomAddMonoidHom L M)

end Additive

end

end SheafOfModules.RingedSite

end
