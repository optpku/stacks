module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.BaseChange
public import stacks_project.Chap59.Lemma_59_54_1
public import stacks_project.Chap59.Lemma_59_80_9_Pullback
public import stacks_project.Chap63.Lemma_63_3_4_LowerShriek

/-!
# Base change comparison for underived étale lower shriek

For a cartesian square of schemes with `f` separated and locally of finite
type, the Sites pullback mate `g⁻¹ f_* ⟶ f'_* (g')⁻¹` restricts along the
compact-support inclusions to a comparison `g⁻¹ f_! ⟶ f'_! (g')⁻¹`.
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

/- The compact-support comparison retains its functorial type. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekBaseChange f g f' g' h_cart :
  etaleLowerShriek f ⋙ etaleAbelianSheafPullback g ⟶
    etaleAbelianSheafPullback g' ⋙ etaleLowerShriek f')

/- Its component is a morphism of abelian sheaves on the new base. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekBaseChange_app f g f' g' h_cart :
  ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    (etaleAbelianSheafPullback g).obj ((etaleLowerShriek f).obj F) ⟶
      (etaleLowerShriek f').obj ((etaleAbelianSheafPullback g').obj F))

/- The compact-support comparison restricts the ordinary base-change mate. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekBaseChange_ι f g f' g' h_cart :
  etaleLowerShriekBaseChange f g f' g' h_cart ≫
      whiskerLeft (etaleAbelianSheafPullback g') (etaleLowerShriekι f') =
    etaleLowerShriekBaseChangeToPushforward f g f' g' h_cart)

end AlgebraicGeometry.Scheme.Etale

end
