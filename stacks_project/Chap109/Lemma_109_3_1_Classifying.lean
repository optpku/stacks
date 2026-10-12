/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import stacks_project.Chap78.Lemma_78_20_2_Atlas
public import stacks_project.Chap99.Lemma_99_15_2
public import stacks_project.Chap109.Lemma_109_3_1_Family

/-!
# Classifying morphisms of algebraic spaces into the stack of curves

A family of curves over an algebraic space `T` determines a cartesian functor
`𝒮_T ⟶ Curves` over `Sch/S` by pulling the family back along scheme-valued
points of `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The Hom-category `Mor(T, Curves)` of cartesian functors from the stack in
sets associated to an algebraic space `T` into the stack of curves, over
`Sch/S`. -/
abbrev Mor {S : Scheme.{u}} (T : AlgebraicSpace S) :=
  CartesianBasedFunctor (stackInSets T).p (p S)

/-- A cartesian functor `𝒮_T ⟶ Curves` lies strictly over `Sch/S`. -/
theorem mor_w {S : Scheme.{u}} {T : AlgebraicSpace S} (F : Mor T) :
    F.toFunctor ⋙ p S = (stackInSets T).p :=
  sorry

/-- The scheme over `S` underlying an object of `𝒮_T`. -/
abbrev pointBase {S : Scheme.{u}} {T : AlgebraicSpace S}
    (x : (stackInSets T).total) : Over S :=
  x.unop.fst.unop

/-- `pointBase x` is the scheme underlying the category-of-elements object `x`. -/
theorem pointBase_spec {S : Scheme.{u}} {T : AlgebraicSpace S}
    (x : (stackInSets T).total) : pointBase x = x.unop.fst.unop :=
  sorry

/-- The morphism `ofOver U ⟶ T` stored by a scheme-valued point of `T`. -/
def pointHom {S : Scheme.{u}} {T : AlgebraicSpace S}
    (x : (stackInSets T).total) : ofOver (pointBase x) ⟶ T :=
  yonedaEquiv.symm x.unop.snd

/-- `pointHom x` is the Yoneda transpose of the functor-of-points value of `x`. -/
theorem pointHom_spec {S : Scheme.{u}} {T : AlgebraicSpace S}
    (x : (stackInSets T).total) :
    pointHom x = yonedaEquiv.symm x.unop.snd :=
  sorry

/-- The morphism of bases over `S` underlying a morphism of `𝒮_T`. -/
def pointMap {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : (stackInSets T).total} (f : x ⟶ y) : pointBase x ⟶ pointBase y :=
  f.unop.val.unop

/-- `pointMap f` is the opposite of the underlying morphism in the category of
elements. -/
theorem pointMap_spec {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : (stackInSets T).total} (f : x ⟶ y) :
    pointMap f = f.unop.val.unop :=
  sorry

/-- Package a commutative square of algebraic spaces as a morphism of families
of curves over schemes over `S`. -/
def homMk {S : Scheme.{u}} {P Q : Obj S} (left : space P ⟶ space Q)
    (right : base P ⟶ base Q)
    (w : left ≫ hom Q = hom P ≫ (ofOverFunctor S).map right) : P ⟶ Q :=
  { hom :=
      { hom :=
          ⟨{ hom := { left := left, right := right, w := w } }, sorry⟩ } }

/-- The algebraic-space component of `homMk left right w` is `left`. -/
theorem homMk_left {S : Scheme.{u}} {P Q : Obj S} (left : space P ⟶ space Q)
    (right : base P ⟶ base Q)
    (w : left ≫ hom Q = hom P ≫ (ofOverFunctor S).map right) :
    spaceMap (homMk left right w) = left :=
  sorry

/-- The base-scheme component of `homMk left right w` is `right`. -/
theorem homMk_right {S : Scheme.{u}} {P Q : Obj S} (left : space P ⟶ space Q)
    (right : base P ⟶ base Q)
    (w : left ≫ hom Q = hom P ≫ (ofOverFunctor S).map right) :
    baseMap (homMk left right w) = right :=
  sorry

/-- The total functor sending a scheme-valued point of `T` to the base change of
a family of curves along that point. -/
def classifyingToObj {S : Scheme.{u}} {T : AlgebraicSpace S} (P : FamilyOver T) :
    (stackInSets T).total ⥤ Obj S where
  obj x := mk (pullback.snd (FamilyOver.hom P) (pointHom x))
  map {x y} f :=
    homMk
      (pullback.map (FamilyOver.hom P) (pointHom x) (FamilyOver.hom P)
        (pointHom y) (𝟙 _) (ofOverMap (pointMap f)) (𝟙 T) sorry sorry)
      (pointMap f) sorry
  map_id := sorry
  map_comp := sorry

/-- On objects, `classifyingToObj P` packages the pullback of the family along
the scheme-valued point. -/
theorem classifyingToObj_obj {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) (x : (stackInSets T).total) :
    (classifyingToObj P).obj x =
      mk (pullback.snd (FamilyOver.hom P) (pointHom x)) :=
  sorry

/-- The classifying cartesian functor `𝒮_T ⟶ Curves` associated to a family of
curves over `T`. -/
def classifyingFunctor {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) : Mor T :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (classifyingToObj P) sorry)

/-- The underlying total functor of `classifyingFunctor P` is
`classifyingToObj P`. -/
theorem classifyingFunctor_toFunctor {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) :
    (classifyingFunctor P).toFunctor = classifyingToObj P :=
  sorry

/-- The total-space component of an isomorphism of families over `T`. -/
def familySpaceMap {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FamilyOver T}
    (φ : P ⟶ Q) : FamilyOver.space P ⟶ FamilyOver.space Q :=
  φ.iso.hom.hom.left

/-- `familySpaceMap φ` is the left component of the underlying morphism in
`Over T`. -/
theorem familySpaceMap_eq {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FamilyOver T} (φ : P ⟶ Q) :
    familySpaceMap φ = φ.iso.hom.hom.left :=
  sorry

/-- The classifying functor sending a family of curves over `T` to the associated
cartesian functor `𝒮_T ⟶ Curves`. -/
def classifying {S : Scheme.{u}} (T : AlgebraicSpace S) :
    FamilyOver T ⥤ Mor T where
  obj := classifyingFunctor
  map φ :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦
          homMk
            (pullback.map (FamilyOver.hom _) (pointHom x) (FamilyOver.hom _)
              (pointHom x) (familySpaceMap φ) (𝟙 _) (𝟙 T) sorry sorry)
            (𝟙 (pointBase x)) sorry
        naturality := sorry
        isHomLift' := sorry }
  map_id := sorry
  map_comp := sorry

/-- On objects, `classifying T` sends a family to `classifyingFunctor` of that
family. -/
theorem classifying_obj {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) : (classifying T).obj P = classifyingFunctor P :=
  sorry

/-- The value of `classifying T` at a family and a scheme-valued point is the
packaged pullback family over that point. -/
theorem classifying_obj_point {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FamilyOver T) (x : (stackInSets T).total) :
    ((classifying T).obj P).toFunctor.obj x =
      mk (pullback.snd (FamilyOver.hom P) (pointHom x)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
