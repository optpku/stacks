/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products and constant module sheaves

For a finitely presented module `Q`, tensoring sections of a constant module
sheaf by `Q` is again a sheaf and agrees canonically with the constant sheaf
of the tensor product.  The comparison map is exposed before its isomorphism
property so downstream code can use its defining universal map.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory Opposite

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {R : Type w} [CommRing R]

namespace ConstantSheaf

/-- The presheaf `U ↦ M̲(U) ⊗[R] Q` obtained by tensoring the sections of a
constant module sheaf by a fixed module. -/
abbrev tensorSections
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]
    (M Q : ModuleCat.{w} R) : Cᵒᵖ ⥤ ModuleCat.{w} R :=
  ((constantSheaf J (ModuleCat.{w} R)).obj M).obj ⋙ tensorRight Q

/-- The canonical presheaf comparison from the constant presheaf on `M ⊗ Q`
to `U ↦ M̲(U) ⊗ Q`. -/
abbrev tensorComparisonNatTrans
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]
    (M Q : ModuleCat.{w} R) :
    (Functor.const Cᵒᵖ).obj (M ⊗ Q) ⟶ tensorSections J M Q :=
  (Functor.constComp Cᵒᵖ M (tensorRight Q)).inv ≫
    Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M)) (tensorRight Q)

/-- Tensoring sections of a constant module sheaf by a finitely presented
module produces a sheaf. -/
theorem tensorSections_isSheaf
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]
    (M Q : ModuleCat.{w} R) [Module.FinitePresentation R Q] :
    Presheaf.IsSheaf J (tensorSections J M Q) := sorry

/-- The sheaf whose sections are `M̲(U) ⊗[R] Q`. -/
noncomputable abbrev tensorSheaf
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]
    (M Q : ModuleCat.{w} R) [Module.FinitePresentation R Q] :
    Sheaf J (ModuleCat.{w} R) :=
  ⟨tensorSections J M Q, tensorSections_isSheaf J M Q⟩

/-- The canonical sheaf morphism `M ⊗ Q̲ ⟶ (U ↦ M̲(U) ⊗ Q)`. -/
noncomputable def tensorComparison
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]
    (M Q : ModuleCat.{w} R) [Module.FinitePresentation R Q] :
    (constantSheaf J (ModuleCat.{w} R)).obj (M ⊗ Q) ⟶
      tensorSheaf J M Q :=
  ObjectProperty.homMk <|
    sheafifyLift J (tensorComparisonNatTrans J M Q)
      (tensorSections_isSheaf J M Q)

/-- The tensor comparison for a finitely presented module is an isomorphism. -/
noncomputable instance tensorComparison_isIso
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]
    (M Q : ModuleCat.{w} R) [Module.FinitePresentation R Q] :
    IsIso (tensorComparison J M Q) := sorry

/-- Lemma 18.42.2 (093K): the canonical sheaf isomorphism
`M ⊗ Q̲ ≅ (U ↦ M̲(U) ⊗[R] Q)` for finitely presented `Q`. -/
@[stacks 093K]
noncomputable def tensorIso
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]
    (M Q : ModuleCat.{w} R) [Module.FinitePresentation R Q] :
    (constantSheaf J (ModuleCat.{w} R)).obj (M ⊗ Q) ≅
      tensorSheaf J M Q :=
  asIso (tensorComparison J M Q)

/-- Evaluating `tensorIso` gives the canonical sectionwise
tensor comparison. -/
noncomputable def tensorAppIso
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]
    (M Q : ModuleCat.{w} R) [Module.FinitePresentation R Q] (U : C) :
    ((constantSheaf J (ModuleCat.{w} R)).obj (M ⊗ Q)).obj.obj (op U) ≅
      (tensorSheaf J M Q).obj.obj (op U) :=
  ((sheafToPresheaf J (ModuleCat.{w} R)).mapIso
    (tensorIso J M Q)).app (op U)

/-- The forward map of the tensor isomorphism is the canonical comparison. -/
@[simp]
theorem tensorIso_hom
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]
    (M Q : ModuleCat.{w} R) [Module.FinitePresentation R Q] :
    (tensorIso J M Q).hom = tensorComparison J M Q := sorry

end ConstantSheaf

end CategoryTheory
