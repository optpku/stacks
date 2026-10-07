module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import ReasLib.CategoryTheory.Adjunction.BaseChange
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

/-- Pullback of abelian small-étale sheaves along a composite is the composite
pullback. -/
def etaleLowerShriekBaseChange_pullbackComp {A B C : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) :
    etaleAbelianSheafPullback p ⋙ etaleAbelianSheafPullback q ≅
      etaleAbelianSheafPullback (q ≫ p) :=
  let siteIso :
      smallEtalePullback p ⋙ smallEtalePullback q ≅ smallEtalePullback (q ≫ p) :=
    (MorphismProperty.Over.pullbackComp q p).symm
  Adjunction.leftAdjointCompIso
    ((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
      A.smallEtaleTopology B.smallEtaleTopology)
    ((smallEtalePullback q).sheafAdjunctionContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology C.smallEtaleTopology)
    ((smallEtalePullback (q ≫ p)).sheafAdjunctionContinuous AddCommGrpCat.{u}
      A.smallEtaleTopology C.smallEtaleTopology)
    (sheafPushforwardContinuousComp' siteIso AddCommGrpCat.{u}
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

section
variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [IsSeparated f] [LocallyOfFiniteType f]

/-- The inverse-image square of abelian small-étale sheaves associated to a
cartesian square of schemes. -/
def etaleLowerShriekBaseChange_pullbackSquare :
    etaleAbelianSheafPullback g ⋙ etaleAbelianSheafPullback f' ≅
      etaleAbelianSheafPullback f ⋙ etaleAbelianSheafPullback g' :=
  etaleLowerShriekBaseChange_pullbackComp g f' ≪≫
    eqToIso (congrArg (fun h : X' ⟶ Y ↦ etaleAbelianSheafPullback h) h_cart.w.symm) ≪≫
    (etaleLowerShriekBaseChange_pullbackComp f g').symm

/-- The underived Sites pullback mate `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of the cartesian
square, obtained as the right mate of the inverse-image square. -/
def etaleLowerShriekBaseChange_pushforwardMate :
    etaleAbelianPushforward f ⋙ etaleAbelianSheafPullback g ⟶
      etaleAbelianSheafPullback g' ⋙ etaleAbelianPushforward f' :=
  DerivedBaseChange.map
    ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u}
      Y.smallEtaleTopology X.smallEtaleTopology)
    ((smallEtalePullback f').sheafAdjunctionContinuous AddCommGrpCat.{u}
      Y'.smallEtaleTopology X'.smallEtaleTopology)
    (etaleLowerShriekBaseChange_pullbackSquare f g f' g' h_cart)

/-- The composite `g⁻¹ f_! ⟶ g⁻¹ f_* ⟶ f'_* (g')⁻¹` obtained by whiskering the
compact-support inclusion with étale inverse image and then applying the
underived Sites pullback mate of the cartesian square. -/
def etaleLowerShriekBaseChangeToPushforward :
    etaleLowerShriek f ⋙ etaleAbelianSheafPullback g ⟶
      etaleAbelianSheafPullback g' ⋙ etaleAbelianPushforward f' :=
  whiskerRight (etaleLowerShriekι f) (etaleAbelianSheafPullback g) ≫
    etaleLowerShriekBaseChange_pushforwardMate f g f' g' h_cart

variable [IsSeparated f'] [LocallyOfFiniteType f']

/-- Whiskering the compact-support inclusion `f'_! ⟶ f'_*` on the left by
`(g')⁻¹` remains a monomorphism. -/
instance etaleLowerShriekι_whiskerLeft_mono :
    Mono (whiskerLeft (etaleAbelianSheafPullback g') (etaleLowerShriekι f')) :=
  sorry

/-- The underived Sites pullback mate sends `g⁻¹ f_!` into the compact-support
subfunctor `f'_! (g')⁻¹` of `f'_* (g')⁻¹`. -/
theorem etaleLowerShriekBaseChange_factors :
    MonoOver.Factors
      (MonoOver.mk
        (whiskerLeft (etaleAbelianSheafPullback g') (etaleLowerShriekι f')))
      (etaleLowerShriekBaseChangeToPushforward f g f' g' h_cart) :=
  sorry

/-- The canonical comparison `g⁻¹ f_! ⟶ f'_! (g')⁻¹` obtained by uniquely
factoring the Sites pullback mate through the compact-support inclusion
`f'_! ⟶ f'_*`. -/
def etaleLowerShriekBaseChange :
    etaleLowerShriek f ⋙ etaleAbelianSheafPullback g ⟶
      etaleAbelianSheafPullback g' ⋙ etaleLowerShriek f' :=
  MonoOver.factorThru
    (MonoOver.mk
      (whiskerLeft (etaleAbelianSheafPullback g') (etaleLowerShriekι f')))
    (etaleLowerShriekBaseChangeToPushforward f g f' g' h_cart)
    (etaleLowerShriekBaseChange_factors f g f' g' h_cart)

/-- The comparison at an abelian étale sheaf `F`. -/
def etaleLowerShriekBaseChange_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback g).obj ((etaleLowerShriek f).obj F) ⟶
      (etaleLowerShriek f').obj ((etaleAbelianSheafPullback g').obj F) :=
  (etaleLowerShriekBaseChange f g f' g' h_cart).app F

/-- The comparison fills the triangle with compact-support inclusions and the
underived Sites pullback mate. -/
theorem etaleLowerShriekBaseChange_ι :
    etaleLowerShriekBaseChange f g f' g' h_cart ≫
        whiskerLeft (etaleAbelianSheafPullback g') (etaleLowerShriekι f') =
      etaleLowerShriekBaseChangeToPushforward f g f' g' h_cart :=
  sorry

/-- Any morphism making the compact-support triangle commute equals the
canonical comparison. -/
theorem etaleLowerShriekBaseChange_lift_unique
    (α : etaleLowerShriek f ⋙ etaleAbelianSheafPullback g ⟶
      etaleAbelianSheafPullback g' ⋙ etaleLowerShriek f')
    (hα : α ≫ whiskerLeft (etaleAbelianSheafPullback g') (etaleLowerShriekι f') =
      etaleLowerShriekBaseChangeToPushforward f g f' g' h_cart) :
    α = etaleLowerShriekBaseChange f g f' g' h_cart :=
  sorry

/-- The comparison `g⁻¹ f_! ⟶ f'_! (g')⁻¹` is an isomorphism. -/
instance etaleLowerShriekBaseChange_isIso :
    IsIso (etaleLowerShriekBaseChange f g f' g' h_cart) :=
  sorry

end

section

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f]

/-- Specialization of the compact-support base-change comparison to the chosen
pullback square of `g` and `f`. -/
def etaleLowerShriekBaseChangeIso_pullback :
    etaleLowerShriek f ⋙ etaleAbelianSheafPullback g ≅
      etaleAbelianSheafPullback (pullback.snd g f) ⋙
        etaleLowerShriek (pullback.fst g f) :=
  asIso
    (etaleLowerShriekBaseChange f g (pullback.fst g f) (pullback.snd g f)
      (IsPullback.of_hasPullback g f).flip)

end

end AlgebraicGeometry.Scheme.Etale

end
