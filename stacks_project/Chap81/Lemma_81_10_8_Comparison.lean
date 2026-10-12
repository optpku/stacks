/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap81.«81_10_6_2_Reverse»
public import stacks_project.Chap81.Lemma_81_10_8_BaseChange

/-!
# Comparison cells for flat base change of formal glueing

The glueing functor and the reverse kernel of a triple are compared with
quasi-coherent pullback along a morphism `g : X' ⟶ X` by named morphisms, later
shown to be isomorphisms when `g` is flat.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QCoh
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

/-- The first component of the glueing-base-change comparison at `F`. -/
def functorBaseChangeNatTrans_fst {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] (F : QCoh X) :
    (pullback (complementBaseChange i g)).obj
        ((pullback (closedImmersionComplementι i)).obj F) ⟶
      (pullback (closedImmersionComplementι (i' i g))).obj ((pullback g).obj F) :=
  ((pullbackCompIso (complementBaseChange i g) (closedImmersionComplementι i)).symm ≪≫
      eqToIso (congrArg pullback (complementBaseChange_comp i g)) ≪≫
      pullbackCompIso (closedImmersionComplementι (i' i g)) g).hom.app F

/-- The second component of the glueing-base-change comparison at `F`. -/
def functorBaseChangeNatTrans_snd {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] (F : QCoh X) :
    (pullback (toY f g)).obj ((pullback f).obj F) ⟶
      (pullback (f' f g)).obj ((pullback g).obj F) :=
  ((pullbackCompIso (toY f g) f).symm ≪≫
      eqToIso (congrArg pullback (Y'_fst f g)) ≪≫
      pullbackCompIso (f' f g) g).hom.app F

/-- The component of the glueing-base-change comparison at a quasi-coherent module `F`. -/
def functorBaseChangeNatTrans_app {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] (F : QCoh X) :
    (baseChange f i g).obj ((functor f i).obj F) ⟶
      (functor (f' f g) (i' i g)).obj ((pullback g).obj F) where
  fst := functorBaseChangeNatTrans_fst f i g F
  snd := functorBaseChangeNatTrans_snd f i g F
  w := sorry

/-- The comparison cell between glueing after pullback and pullback after glueing. -/
def functorBaseChangeNatTrans {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    functor f i ⋙ baseChange f i g ⟶
      pullback g ⋙ functor (f' f g) (i' i g) where
  app F := functorBaseChangeNatTrans_app f i g F
  naturality := sorry

/-- The component of `functorBaseChangeNatTrans` at `F` is `functorBaseChangeNatTrans_app`. -/
theorem functorBaseChangeNatTrans_app_eq {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] (F : QCoh X) :
    (functorBaseChangeNatTrans f i g).app F = functorBaseChangeNatTrans_app f i g F :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

namespace AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing

/-- Cartesian identification of successive module pullbacks along the complement square. -/
def complementCartesianIso {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    pullback g ⋙ pullback (j (QCoh.FormalGlueing.i' i g)) ≅
      pullback (j i) ⋙ pullback (QCoh.FormalGlueing.complementBaseChange i g) :=
  pullbackCompIso (j (QCoh.FormalGlueing.i' i g)) g ≪≫
    eqToIso (congrArg pullback (QCoh.FormalGlueing.complementBaseChange_comp i g).symm) ≪≫
    (pullbackCompIso (QCoh.FormalGlueing.complementBaseChange i g) (j i)).symm

/-- The underived base-change cell `g^* j_* ⟶ j'_* u^*` of complement pushforwards. -/
def complementPushforwardBaseChangeNatTrans {S : Scheme.{u}} {X Z X' : AlgebraicSpace S}
    (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i] :
    pushforward (j i) ⋙ pullback g ⟶
      pullback (QCoh.FormalGlueing.complementBaseChange i g) ⋙
        pushforward (j (QCoh.FormalGlueing.i' i g)) :=
  CategoryTheory.DerivedBaseChange.map (pullbackPushforwardAdjunction (j i))
    (pullbackPushforwardAdjunction (j (QCoh.FormalGlueing.i' i g)))
    (complementCartesianIso i g)

/-- The pulled-back reverse comparison morphism of a glueing triple `(H, G, φ)`. -/
def pulledBackφ {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    (pullback (restrictF (QCoh.FormalGlueing.f' f g) (QCoh.FormalGlueing.i' i g))).obj
        ((pullback (QCoh.FormalGlueing.complementBaseChange i g)).obj H) ⟶
      restrict ((pullback (QCoh.FormalGlueing.toY f g)).obj G)
        (j' (QCoh.FormalGlueing.f' f g) (QCoh.FormalGlueing.i' i g)) :=
  (pullbackCompIso (restrictF (QCoh.FormalGlueing.f' f g) (QCoh.FormalGlueing.i' i g))
      (QCoh.FormalGlueing.complementBaseChange i g)).hom.app H ≫
    eqToHom (congrArg (fun h ↦ (pullback h).obj H)
      (overlapBaseChange_comp_restrictF f i g).symm) ≫
    (pullbackCompIso (overlapBaseChange f i g) (restrictF f i)).inv.app H ≫
    (pullback (overlapBaseChange f i g)).map φ ≫
    (pullback (overlapBaseChange f i g)).map
      ((restrictFunctorIsoPullback (j' f i)).hom.app G) ≫
    (pullbackCompIso (overlapBaseChange f i g) (j' f i)).hom.app G ≫
    eqToHom (congrArg (fun h ↦ (pullback h).obj G) (overlapBaseChange_comp_j' f i g)) ≫
    (pullbackCompIso (j' (QCoh.FormalGlueing.f' f g) (QCoh.FormalGlueing.i' i g))
      (QCoh.FormalGlueing.toY f g)).inv.app G ≫
    (restrictFunctorIsoPullback
      (j' (QCoh.FormalGlueing.f' f g) (QCoh.FormalGlueing.i' i g))).inv.app
      ((pullback (QCoh.FormalGlueing.toY f g)).obj G)

/-- The comparison morphism `g^* reverse(H, G, φ) ⟶ reverse(H', G', φ')`. -/
def reverseBaseChangeHom {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    (pullback g).obj (reverse f i H G φ) ⟶
      reverse (QCoh.FormalGlueing.f' f g) (QCoh.FormalGlueing.i' i g)
        ((pullback (QCoh.FormalGlueing.complementBaseChange i g)).obj H)
        ((pullback (QCoh.FormalGlueing.toY f g)).obj G) (pulledBackφ f i g H G φ) :=
  kernel.lift
    (comparison (QCoh.FormalGlueing.f' f g) (QCoh.FormalGlueing.i' i g)
      ((pullback (QCoh.FormalGlueing.complementBaseChange i g)).obj H)
      ((pullback (QCoh.FormalGlueing.toY f g)).obj G) (pulledBackφ f i g H G φ))
    ((pullback g).map (kernel.ι (comparison f i H G φ)) ≫
      biprod.lift ((pullback g).map biprod.fst) ((pullback g).map biprod.snd) ≫
      biprod.map ((complementPushforwardBaseChangeNatTrans i g).app H)
        ((pushforwardBaseChangeNatTrans (IsPullback.of_hasPullback f g)).app G))
    sorry

/-- Postcomposing `reverseBaseChangeHom` with the kernel inclusion recovers the
biproduct of the two pushforward base-change cells. -/
theorem reverseBaseChangeHom_eq {S : Scheme.{u}} {X Y Z X' : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) (g : X' ⟶ X) [IsClosedImmersion i]
    (H : (U i).Modules) (G : Y.Modules)
    (φ : (pullback (restrictF f i)).obj H ⟶ restrict G (j' f i)) :
    reverseBaseChangeHom f i g H G φ ≫
        kernel.ι (comparison (QCoh.FormalGlueing.f' f g)
          (QCoh.FormalGlueing.i' i g)
          ((pullback (QCoh.FormalGlueing.complementBaseChange i g)).obj H)
          ((pullback (QCoh.FormalGlueing.toY f g)).obj G) (pulledBackφ f i g H G φ)) =
      (pullback g).map (kernel.ι (comparison f i H G φ)) ≫
        biprod.lift ((pullback g).map biprod.fst) ((pullback g).map biprod.snd) ≫
        biprod.map ((complementPushforwardBaseChangeNatTrans i g).app H)
          ((pushforwardBaseChangeNatTrans (IsPullback.of_hasPullback f g)).app G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.FormalGlueing
