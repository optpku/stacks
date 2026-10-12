/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_4_10_Pullback
public import stacks_project.Chap63.Lemma_63_4_10_Comparison

/-!
# Base change for locally quasi-finite étale lower shriek

Lemma 63.4.10: in a cartesian square of schemes with `f` locally quasi-finite,
compact-support pushforward commutes with étale inverse image on abelian
sheaves, compatibly with the stalk formula of Lemma 63.4.5.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']

/-- Lemma 63.4.10: Consider a cartesian square of schemes with `f` locally
quasi-finite. There is an isomorphism `g⁻¹ f_! F ≅ f'_! ((g')⁻¹ F)` functorial
for `F` in `Ab(X_étale)`, compatible with the stalk descriptions of
Lemma 63.4.5. -/
@[stacks 0F5J]
def lowerShriekBaseChangeIso :
    lowerShriek f ⋙ etaleAbelianSheafPullback g ≅
      etaleAbelianSheafPullback g' ⋙ lowerShriek f' :=
  asIso (lowerShriekBaseChange f g f' g' h_cart)

/-- The objectwise identification `g⁻¹ (f_! F) ≅ f'_! ((g')⁻¹ F)` at an abelian
étale sheaf `F`. -/
def lowerShriekBaseChangeIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback g).obj ((lowerShriek f).obj F) ≅
      (lowerShriek f').obj ((etaleAbelianSheafPullback g').obj F) :=
  (lowerShriekBaseChangeIso f g f' g' h_cart).app F

/-- The forward map of `lowerShriekBaseChangeIso` is the constructed
base-change comparison. -/
theorem lowerShriekBaseChangeIso_hom :
    (lowerShriekBaseChangeIso f g f' g' h_cart).hom =
      lowerShriekBaseChange f g f' g' h_cart :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
