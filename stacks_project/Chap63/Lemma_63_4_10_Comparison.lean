/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap63.Definition_63_4_4_LowerShriek
public import stacks_project.Chap63.Lemma_63_4_10_Pullback
public import stacks_project.Chap63.Lemma_63_4_5

/-!
# Base-change comparison for locally quasi-finite lower shriek

For a cartesian square of schemes with `f` locally quasi-finite, the presheaf
map `c : f_{p!} F ⟶ g_* f'_{p!} (g')⁻¹ F` sheafifies to a comparison
`g⁻¹ f_! ⟶ f'_! (g')⁻¹` of abelian étale sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale.FiniteSupport

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']

/-- The source map `c : f_{p!} ⟶ g_* f'_{p!} (g')⁻¹` of abelian étale
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
theorem lowerShriekPresheafBaseChange_ofTerm
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
theorem lowerShriekBaseChange_app_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekBaseChange_app f g f' g' h_cart F =
      sheafifyPresheafPushforwardAdjoint g
        (lowerShriekPresheafBaseChange_app f g f' g' h_cart F) :=
  sorry

/-- The comparison `g⁻¹ f_! ⟶ f'_! (g')⁻¹` is an isomorphism. -/
instance lowerShriekBaseChange_isIso :
    IsIso (lowerShriekBaseChange f g f' g' h_cart) :=
  sorry

/-- Compatibility of the base-change comparison with the stalk identifications
of Lemma 63.4.5. -/
theorem lowerShriekBaseChangeIso_stalk (ybar' : GeometricPoint Y')
    [InitiallySmall
      ((smallEtalePullback g ⋙ (toSmallEtalePoint ybar').fiber).Elements)]
    [∀ x' : Over f' ybar',
      InitiallySmall
        ((smallEtalePullback g' ⋙
            (toSmallEtalePoint x'.toGeometricPoint).fiber).Elements)]
    [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
    [HasProducts.{u} AddCommGrpCat.{u}]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    CommSq
      ((pullbackSheafFiberIso g ybar' ((lowerShriek f).obj F)).inv ≫
        ((lowerShriekStalkIso f (imageGeometricPoint g ybar')).app F).hom)
      ((toSmallEtalePoint ybar').sheafFiber.map
        (lowerShriekBaseChange_app f g f' g' h_cart F))
      ((abelianStalkCoproductBaseChangeIso f g f' g' h_cart ybar').app F).hom
      ((lowerShriekStalkIso f' ybar').app
          ((etaleAbelianSheafPullback g').obj F)).hom :=
  sorry

end

section

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]

/-- Specialization of the locally quasi-finite base-change comparison to the
chosen pullback square of `g` and `f`. -/
def lowerShriekBaseChangeIso_pullback :
    lowerShriek f ⋙ etaleAbelianSheafPullback g ≅
      etaleAbelianSheafPullback (pullback.snd g f) ⋙
        lowerShriek (pullback.fst g f) :=
  asIso
    (lowerShriekBaseChange f g (pullback.fst g f) (pullback.snd g f)
      (IsPullback.of_hasPullback g f).flip)

end

end AlgebraicGeometry.Scheme.Etale

end
