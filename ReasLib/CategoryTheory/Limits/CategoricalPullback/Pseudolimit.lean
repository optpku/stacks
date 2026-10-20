module

import Mathlib.CategoryTheory.Category.Cat.Terminal
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Cat.Evaluation
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.PseudoCone

/-!
# The categorical pullback as a conical pseudolimit

This module compares mathlib's explicit categorical pullback with the neutral representable
conical pseudolimit of the corresponding walking-cospan pseudofunctor.

The equivalence `conicalPseudoLimitEquivalence` retains the specified comparison functor and
constructs its inverse by evaluating pseudocones at the canonical terminal point. Its unit and
counit are explicit natural isomorphisms, and it supplies the comparison's `IsEquivalence`
instance.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe v u

namespace CategoryTheory

open Bicategory
open Limits
open Limits.CategoricalPullback
open scoped Pseudofunctor.StrongTrans
open scoped Limits.CategoricalPullback

namespace Limits.CategoricalPullback

variable {A B C : Type u}
variable [Category.{v} A] [Category.{v} B] [Category.{v} C]

/-- The canonical comparison from mathlib's explicit categorical pullback to the neutral
conical pseudolimit category of the associated walking-cospan pseudofunctor.

It first regards an object as a constant functor out of the chosen terminal category, then
uses mathlib's `CategoricalPullback.functorEquiv` to obtain a categorical commutative square,
and finally interprets that square as a walking-cospan pseudocone. -/
noncomputable def toConicalPseudoLimit (F : A ⥤ C) (G : B ⥤ C) :
    F ⊡ G ⥤
      ConicalPseudoLimit.coneCategory (Bicategory.cospan F.toCatHom G.toCatHom) :=
  Functor.const (⊤_ Cat) ⋙ (functorEquiv F G (⊤_ Cat)).functor ⋙
    CatCommSqOver.toPseudoConeFunctor (⊤_ Cat) F G

/-- Recover a categorical-pullback object from a terminal-apex pseudocone. The structural
isomorphism passes through the component at the central vertex of the cospan. -/
noncomputable def fromConicalPseudoLimit (F : A ⥤ C) (G : B ⥤ C) :
    ConicalPseudoLimit.coneCategory (Bicategory.cospan F.toCatHom G.toCatHom) ⥤ F ⊡ G where
  obj P :=
    { fst := (P.app (LocallyDiscrete.mk WalkingCospan.left)).toFunctor.obj
        ConicalPseudoLimit.terminalPoint
      snd := (P.app (LocallyDiscrete.mk WalkingCospan.right)).toFunctor.obj
        ConicalPseudoLimit.terminalPoint
      iso := (Cat.Hom.toNatIso
        ((P.naturality (Quiver.Hom.toLoc WalkingCospan.Hom.inl)).symm ≪≫
          P.naturality (Quiver.Hom.toLoc WalkingCospan.Hom.inr))).app
            ConicalPseudoLimit.terminalPoint }
  map η :=
    { fst := (η.as.app (LocallyDiscrete.mk WalkingCospan.left)).toNatTrans.app
        ConicalPseudoLimit.terminalPoint
      snd := (η.as.app (LocallyDiscrete.mk WalkingCospan.right)).toNatTrans.app
        ConicalPseudoLimit.terminalPoint
      w := by sorry }
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The first projection of the recovered object is evaluation at the left vertex. -/
@[simp]
theorem fromConicalPseudoLimit_obj_fst (F : A ⥤ C) (G : B ⥤ C)
    (P : ConicalPseudoLimit.coneCategory (Bicategory.cospan F.toCatHom G.toCatHom)) :
    ((fromConicalPseudoLimit F G).obj P).fst =
      (P.app (LocallyDiscrete.mk WalkingCospan.left)).toFunctor.obj
        ConicalPseudoLimit.terminalPoint := rfl

/-- The second projection of the recovered object is evaluation at the right vertex. -/
@[simp]
theorem fromConicalPseudoLimit_obj_snd (F : A ⥤ C) (G : B ⥤ C)
    (P : ConicalPseudoLimit.coneCategory (Bicategory.cospan F.toCatHom G.toCatHom)) :
    ((fromConicalPseudoLimit F G).obj P).snd =
      (P.app (LocallyDiscrete.mk WalkingCospan.right)).toFunctor.obj
        ConicalPseudoLimit.terminalPoint := rfl

/-- The recovered structural isomorphism is the composite of the two cone generators. -/
@[simp]
theorem fromConicalPseudoLimit_obj_iso (F : A ⥤ C) (G : B ⥤ C)
    (P : ConicalPseudoLimit.coneCategory (Bicategory.cospan F.toCatHom G.toCatHom)) :
    ((fromConicalPseudoLimit F G).obj P).iso =
      (Cat.Hom.toNatIso
        ((P.naturality (Quiver.Hom.toLoc WalkingCospan.Hom.inl)).symm ≪≫
          P.naturality (Quiver.Hom.toLoc WalkingCospan.Hom.inr))).app
            ConicalPseudoLimit.terminalPoint := rfl

/-- The first component of a recovered arrow is evaluation of its left modification. -/
@[simp]
theorem fromConicalPseudoLimit_map_fst (F : A ⥤ C) (G : B ⥤ C)
    {P Q : ConicalPseudoLimit.coneCategory (Bicategory.cospan F.toCatHom G.toCatHom)}
    (η : P ⟶ Q) :
    ((fromConicalPseudoLimit F G).map η).fst =
      (η.as.app (LocallyDiscrete.mk WalkingCospan.left)).toNatTrans.app
        ConicalPseudoLimit.terminalPoint := rfl

/-- The second component of a recovered arrow is evaluation of its right modification. -/
@[simp]
theorem fromConicalPseudoLimit_map_snd (F : A ⥤ C) (G : B ⥤ C)
    {P Q : ConicalPseudoLimit.coneCategory (Bicategory.cospan F.toCatHom G.toCatHom)}
    (η : P ⟶ Q) :
    ((fromConicalPseudoLimit F G).map η).snd =
      (η.as.app (LocallyDiscrete.mk WalkingCospan.right)).toNatTrans.app
        ConicalPseudoLimit.terminalPoint := rfl

/-- Every object of the chosen terminal category equals its specified point. -/
private theorem terminalPoint_eq (x : ⊤_ Cat.{v, u}) :
    ConicalPseudoLimit.terminalPoint = x := by
  have h : ((Functor.const (⊤_ Cat)).obj
      ConicalPseudoLimit.terminalPoint).toCatHom = 𝟙 (⊤_ Cat) :=
    terminalIsTerminal.hom_ext _ _
  exact congrArg (fun f : (⊤_ Cat) ⟶ (⊤_ Cat) ↦ f.toFunctor.obj x) h

/-- Evaluation after taking the constant pseudocone recovers both projections identically. -/
private noncomputable def conicalPseudoLimitUnitIso (F : A ⥤ C) (G : B ⥤ C) :
    𝟭 (F ⊡ G) ≅ toConicalPseudoLimit F G ⋙ fromConicalPseudoLimit F G :=
  NatIso.ofComponents
    (fun P ↦ CategoricalPullback.mkIso (Iso.refl P.fst) (Iso.refl P.snd) (by sorry))
    (by
      intro P Q f
      ext
      · change f.fst ≫ 𝟙 Q.fst = 𝟙 P.fst ≫ f.fst
        simp
      · change f.snd ≫ 𝟙 Q.snd = 𝟙 P.snd ≫ f.snd
        simp)

/-- The components comparing a reconstructed pseudocone with the original pseudocone. -/
private noncomputable def conicalPseudoLimitCounitApp (F : A ⥤ C) (G : B ⥤ C)
    (P : ConicalPseudoLimit.coneCategory (Bicategory.cospan F.toCatHom G.toCatHom)) :
    (j : LocallyDiscrete WalkingCospan) →
      ((fromConicalPseudoLimit F G ⋙ toConicalPseudoLimit F G).obj P).app j ≅ P.app j
  | ⟨WalkingCospan.one⟩ => Cat.Hom.isoMk <| NatIso.ofComponents
      (fun x ↦
        ((Cat.Hom.toNatIso
          (P.naturality (Quiver.Hom.toLoc WalkingCospan.Hom.inl))).app
            ConicalPseudoLimit.terminalPoint).symm ≪≫
          (P.app (LocallyDiscrete.mk WalkingCospan.one)).toFunctor.mapIso
            (eqToIso (terminalPoint_eq x)))
      (by sorry)
  | ⟨WalkingCospan.left⟩ => Cat.Hom.isoMk <| NatIso.ofComponents
      (fun x ↦ (P.app (LocallyDiscrete.mk WalkingCospan.left)).toFunctor.mapIso
        (eqToIso (terminalPoint_eq x)))
      (by sorry)
  | ⟨WalkingCospan.right⟩ => Cat.Hom.isoMk <| NatIso.ofComponents
      (fun x ↦ (P.app (LocallyDiscrete.mk WalkingCospan.right)).toFunctor.mapIso
        (eqToIso (terminalPoint_eq x)))
      (by sorry)

/-- Reconstruction is naturally isomorphic to the original terminal-apex pseudocone. -/
private noncomputable def conicalPseudoLimitCounitIso (F : A ⥤ C) (G : B ⥤ C) :
    fromConicalPseudoLimit F G ⋙ toConicalPseudoLimit F G ≅
      𝟭 (ConicalPseudoLimit.coneCategory (Bicategory.cospan F.toCatHom G.toCatHom)) :=
  NatIso.ofComponents
    (fun P ↦ Pseudofunctor.StrongTrans.isoMk
      (conicalPseudoLimitCounitApp F G P) (by sorry))
    (by sorry)

/-- The categorical pullback is equivalent to terminal-apex pseudocones over its cospan,
with inverse given by evaluation of the two legs and their structural isomorphism. -/
noncomputable def conicalPseudoLimitEquivalence (F : A ⥤ C) (G : B ⥤ C) :
    F ⊡ G ≌ ConicalPseudoLimit.coneCategory (Bicategory.cospan F.toCatHom G.toCatHom) where
  functor := toConicalPseudoLimit F G
  inverse := fromConicalPseudoLimit F G
  unitIso := conicalPseudoLimitUnitIso F G
  counitIso := conicalPseudoLimitCounitIso F G
  functor_unitIso_comp := by sorry

/-- The explicit categorical pullback presents the neutral conical pseudolimit of its
walking-cospan pseudofunctor. -/
instance toConicalPseudoLimit.isEquivalence (F : A ⥤ C) (G : B ⥤ C) :
    (toConicalPseudoLimit F G).IsEquivalence :=
  (conicalPseudoLimitEquivalence F G).isEquivalence_functor

/- Data audit (mathlib 4.32): the comparison, inverse, and equivalence report `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. Their objects, arrows, and unit/counit
components are the explicit constructions above. The terminal point and `terminalPoint_eq`
use only mathlib's terminal-category data and laws; neither depends on `sorryAx`. Deferred
proofs are compatibility, naturality, functor and pseudofunctor coherence, and triangle laws.
No inverse data is extracted from the equivalence instance. -/

end Limits.CategoricalPullback

end CategoryTheory
