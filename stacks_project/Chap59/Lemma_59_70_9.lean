/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap59.Lemma_59_54_1
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {U X V Y : Scheme.{u}}
variable (j' : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
variable [IsFinite f] [IsOpenImmersion j] [Etale j] [Etale j']
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j').op.HasLeftKanExtension F]
variable [∀ F : V.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Lemma 59.70.9: for a cartesian square of schemes with finite `f : X ⟶ Y`
and open immersion `j : V ⟶ Y`, the functors `Ab(U_étale) ⥤ Ab(Y_étale)`
satisfy `etaleAbelianPushforward f ∘ abelianExtensionByZero j' ≅
abelianExtensionByZero j ∘ etaleAbelianPushforward g`. -/
@[stacks 0GJ1]
theorem abelianExtensionByZero_comp_etaleAbelianPushforward
    (h_cart : IsPullback j' g f j) :
    Nonempty
      (abelianExtensionByZero j' ⋙ etaleAbelianPushforward f ≅
        etaleAbelianPushforward g ⋙ abelianExtensionByZero j) :=
  sorry

/-- Objectwise form of `abelianExtensionByZero_comp_etaleAbelianPushforward`:
`f_* (j'_! F) ≅ j_! (g_* F)` for an abelian étale sheaf `F` on `U`. -/
theorem abelianExtensionByZero_comp_etaleAbelianPushforward_app
    (h_cart : IsPullback j' g f j)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    Nonempty
      ((etaleAbelianPushforward f).obj ((abelianExtensionByZero j').obj F) ≅
        (abelianExtensionByZero j).obj ((etaleAbelianPushforward g).obj F)) :=
  sorry

end AlgebraicGeometry.Scheme
