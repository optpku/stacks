module

public import stacks_project.Chap63.Lemma_63_3_12_Comparison

/-!
# Base change for underived étale lower shriek

Lemma 63.3.12: in a cartesian square of schemes with `f` separated and locally
of finite type, underived compact-support pushforward commutes with étale
inverse image.
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
variable [IsSeparated f] [LocallyOfFiniteType f]
variable [IsSeparated f'] [LocallyOfFiniteType f']

/-- Lemma 63.3.12: Consider a cartesian square of schemes with `f` separated
and locally of finite type. For any abelian sheaf `F` on `X_étale` we have
`f'_! ((g')⁻¹ F) = g⁻¹ (f_! F)`, as abelian sheaves on `Y'_étale`. -/
@[stacks 0F55]
def etaleLowerShriekBaseChangeIso :
    etaleLowerShriek f ⋙ etaleAbelianSheafPullback g ≅
      etaleAbelianSheafPullback g' ⋙ etaleLowerShriek f' :=
  asIso (etaleLowerShriekBaseChange f g f' g' h_cart)

/-- The objectwise identification `g⁻¹ (f_! F) ≅ f'_! ((g')⁻¹ F)` at an abelian
étale sheaf `F`. -/
def etaleLowerShriekBaseChangeIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback g).obj ((etaleLowerShriek f).obj F) ≅
      (etaleLowerShriek f').obj ((etaleAbelianSheafPullback g').obj F) :=
  (etaleLowerShriekBaseChangeIso f g f' g' h_cart).app F

/-- The forward map of `etaleLowerShriekBaseChangeIso` is the compact-support
base-change comparison. -/
theorem etaleLowerShriekBaseChangeIso_hom :
    (etaleLowerShriekBaseChangeIso f g f' g' h_cart).hom =
      etaleLowerShriekBaseChange f g f' g' h_cart :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
