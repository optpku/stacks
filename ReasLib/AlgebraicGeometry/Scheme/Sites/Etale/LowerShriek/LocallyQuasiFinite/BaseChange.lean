module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Coproduct.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Properties

/-!
# Base change for locally quasi-finite compact-support direct image

Cartesian pullback of supported sections induces a natural comparison on
abelian étale sheaves. Its geometric-stalk coproduct square identifies this
comparison as an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

open AlgebraicGeometry.Scheme.Etale.FiniteSupport

namespace AlgebraicGeometry.Scheme.Etale

section

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f]
variable [LocallyQuasiFinite f']

/-- The finite-support map `c : f_{p!} ⟶ g_* f'_{p!} (g')⁻¹` of abelian étale
presheaves, obtained by colimit of the cartesian pullback of supported
sections. -/
def lowerShriekPresheafBaseChange :
    lowerShriekPresheaf f ⟶
      etaleAbelianSheafPullback g' ⋙ lowerShriekPresheaf f' ⋙
        presheafPushforwardAb g where
  app F :=
    { app := fun V ↦
        colimMap (sectionsBaseChangeNatTrans f g f' g' h_cart F V.unop) ≫
          colimit.pre
            (diagram f' ((etaleAbelianSheafPullback g').obj F)
              ((smallEtalePullback g).obj V.unop))
            (Admissible.baseChangeFunctor f g f' g' h_cart V.unop)
      naturality := sorry }
  naturality := sorry

/-- Evaluating the presheaf comparison at an abelian étale sheaf `F`. -/
def lowerShriekPresheafBaseChange_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekPresheaf f).obj F ⟶
      (presheafPushforwardAb g).obj
        ((lowerShriekPresheaf f').obj ((etaleAbelianSheafPullback g').obj F)) :=
  (lowerShriekPresheafBaseChange f g f' g' h_cart).app F

/-- The presheaf comparison sends the class of a finite-support pair to the
class of its cartesian base change. -/
theorem lowerShriekPresheafBaseChange_ofTerm [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (t : FiniteSupportTerm f F V) :
    ((lowerShriekPresheafBaseChange_app f g f' g' h_cart F).app (op V)).hom
        (ofTerm f F V t) =
      ofTerm f' ((etaleAbelianSheafPullback g').obj F)
        ((smallEtalePullback g).obj V)
        (FiniteSupportTerm.baseChange f g f' g' h_cart t) :=
  sorry

/-- The canonical comparison `g⁻¹ f_! ⟶ f'_! (g')⁻¹` obtained by taking the
sheaf-pushforward adjunct of `lowerShriekPresheafBaseChange`. -/
def lowerShriekBaseChange :
    lowerShriek f ⋙ etaleAbelianSheafPullback g ⟶
      etaleAbelianSheafPullback g' ⋙ lowerShriek f' where
  app F :=
    sheafifyPresheafPushforwardAdjoint g
      (lowerShriekPresheafBaseChange_app f g f' g' h_cart F)
  naturality := sorry

/-- The comparison at an abelian étale sheaf `F`. -/
def lowerShriekBaseChange_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback g).obj ((lowerShriek f).obj F) ⟶
      (lowerShriek f').obj ((etaleAbelianSheafPullback g').obj F) :=
  (lowerShriekBaseChange f g f' g' h_cart).app F

/-- The objectwise comparison is the adjunct of the presheaf map `c`. -/
theorem lowerShriekBaseChange_app_eq [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekBaseChange_app f g f' g' h_cart F =
      sheafifyPresheafPushforwardAdjoint g
        (lowerShriekPresheafBaseChange_app f g f' g' h_cart F) :=
  rfl

/-- The base-change comparison commutes with the geometric-stalk coproduct
identifications and canonical inverse-image stalk maps. -/
theorem lowerShriekBaseChangeIso_stalk [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (ybar' : GeometricPoint Y')
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    CommSq
      ((pullbackSheafFiberIso g ybar' ((lowerShriek f).obj F)).inv ≫
        ((lowerShriekStalkIso f (ybar'.map g)).app F).hom)
      ((toSmallEtalePoint ybar').sheafFiber.map
        (lowerShriekBaseChange_app f g f' g' h_cart F))
      ((abelianStalkCoproductBaseChangeIso f g f' g' h_cart ybar').app F).hom
      ((lowerShriekStalkIso f' ybar').app
          ((etaleAbelianSheafPullback g').obj F)).hom :=
  sorry

/-- The comparison `g⁻¹ f_! ⟶ f'_! (g')⁻¹` is an isomorphism. -/
instance lowerShriekBaseChange_isIso [LocallyOfFiniteType f] [LocallyOfFiniteType f'] :
    IsIso (lowerShriekBaseChange f g f' g' h_cart) :=
  sorry

/-- Cartesian base change commutes naturally with locally quasi-finite compact-support
direct image on abelian étale sheaves. -/
def lowerShriekBaseChangeIso [LocallyOfFiniteType f] [LocallyOfFiniteType f'] :
    lowerShriek f ⋙ etaleAbelianSheafPullback g ≅
      etaleAbelianSheafPullback g' ⋙ lowerShriek f' :=
  asIso (lowerShriekBaseChange f g f' g' h_cart)

/-- The objectwise identification `g⁻¹ (f_! F) ≅ f'_! ((g')⁻¹ F)` at an abelian
étale sheaf `F`. -/
def lowerShriekBaseChangeIso_app [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback g).obj ((lowerShriek f).obj F) ≅
      (lowerShriek f').obj ((etaleAbelianSheafPullback g').obj F) :=
  (lowerShriekBaseChangeIso f g f' g' h_cart).app F

/-- The forward map of `lowerShriekBaseChangeIso` is the constructed
base-change comparison. -/
theorem lowerShriekBaseChangeIso_hom [LocallyOfFiniteType f] [LocallyOfFiniteType f'] :
    (lowerShriekBaseChangeIso f g f' g' h_cart).hom =
      lowerShriekBaseChange f g f' g' h_cart :=
  rfl

end

section

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [LocallyQuasiFinite f]

/-- Specialization of the locally quasi-finite base-change comparison to the
chosen pullback square of `g` and `f`. -/
def lowerShriekBaseChangeIso_pullback [LocallyOfFiniteType f] :
    lowerShriek f ⋙ etaleAbelianSheafPullback g ≅
      etaleAbelianSheafPullback (pullback.snd g f) ⋙
        lowerShriek (pullback.fst g f) :=
  asIso
    (lowerShriekBaseChange f g (pullback.fst g f) (pullback.snd g f)
      (IsPullback.of_hasPullback g f).flip)

end

end AlgebraicGeometry.Scheme.Etale

end
