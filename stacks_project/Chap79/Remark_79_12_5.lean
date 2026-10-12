/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap79.Lemma_79_12_9_Sheaf
public import stacks_project.Chap79.Remark_79_12_5_Algebra
import StacksCheckRecall

/-!
# Finite-part sheaves as non-unital F₂-algebras over the base

A separated morphism `f : X ⟶ Y` of algebraic spaces has a structure map
`(X/Y)_fin ⟶ Y`. Compatible pairs over `Y` carry union, intersection, and
set-difference, making `(X/Y)_fin` a non-unital F₂-algebra over `Y`. If `f` is
finite, the algebra is unital.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Type-valued fppf sheaves on schemes over `S` have pullbacks. -/
instance instHasPullbacks_fppfSheaf (S : Scheme.{u}) :
    HasPullbacks (Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))) :=
  inferInstance

/- Remark 79.12.5 (1): the sheaf `(X/Y)_fin` maps to `Y` by sending a pair
`(a, Z)` to the section `a`. -/
@[stacks 04PI] #check AlgebraicGeometry.AlgebraicSpace.finitePartTo

/-- The first factor of a compatible pair of finite-part sections over `Y`. -/
def starFst {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    FinitePart.Point f T.unop :=
  (pullback.fst (finitePartTo f) (finitePartTo f)).hom.app T s

/-- The second factor of a compatible pair of finite-part sections over `Y`. -/
def starSnd {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    FinitePart.Point f T.unop :=
  (pullback.snd (finitePartTo f) (finitePartTo f)).hom.app T s

/-- Compatible pairs in the self-fibre product over `Y` have the same morphism `a`. -/
theorem star_a_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (starFst f T s).a = (starSnd f T s).a :=
  sorry

/-- Assemble a fibrewise operation on compatible finite-part pairs as a morphism
of sheaves over `Y`. -/
def starMk {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (op : ∀ {T : Over S} (p q : FinitePart.Point f T),
      p.a = q.a → FinitePart.Point f T) :
    pullback (finitePartTo f) (finitePartTo f) ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun s ↦ op (starFst f T s) (starSnd f T s) (star_a_eq f T s)
      naturality := sorry }

/-- Components of `starMk` apply the given fibrewise operation to the two projections. -/
theorem starMk_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (op : ∀ {T : Over S} (p q : FinitePart.Point f T),
      p.a = q.a → FinitePart.Point f T)
    (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (starMk f op).hom.app T s =
      op (starFst f T s) (starSnd f T s) (star_a_eq f T s) :=
  sorry

/-- Remark 79.12.5 (2): union of compatible finite-part pairs over `Y`. -/
@[stacks 04PI]
def star1 {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    pullback (finitePartTo f) (finitePartTo f) ⟶ finitePartSheaf f :=
  starMk f fun p q h ↦ p.union q h

/-- Remark 79.12.5 (3): intersection of compatible finite-part pairs over `Y`. -/
@[stacks 04PI]
def star2 {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    pullback (finitePartTo f) (finitePartTo f) ⟶ finitePartSheaf f :=
  starMk f fun p q h ↦ p.inter q h

/-- Remark 79.12.5 (4): set-difference of compatible finite-part pairs over `Y`. -/
@[stacks 04PI]
def star3 {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    pullback (finitePartTo f) (finitePartTo f) ⟶ finitePartSheaf f :=
  starMk f fun p q h ↦ p.sdiff q h

/-- Remark 79.12.5 (5): swapped set-difference of compatible finite-part pairs over `Y`. -/
@[stacks 04PI]
def star4 {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] :
    pullback (finitePartTo f) (finitePartTo f) ⟶ finitePartSheaf f :=
  starMk f fun p q h ↦ q.sdiff p h.symm

/-- Components of `star1` are fibrewise union of compatible pairs. -/
theorem star1_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (star1 f).hom.app T s =
      (starFst f T s).union (starSnd f T s) (star_a_eq f T s) :=
  sorry

/-- Components of `star2` are fibrewise intersection of compatible pairs. -/
theorem star2_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (star2 f).hom.app T s =
      (starFst f T s).inter (starSnd f T s) (star_a_eq f T s) :=
  sorry

/-- Components of `star3` are fibrewise set-difference of compatible pairs. -/
theorem star3_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (star3 f).hom.app T s =
      (starFst f T s).sdiff (starSnd f T s) (star_a_eq f T s) :=
  sorry

/-- Components of `star4` are the swapped fibrewise set-difference. -/
theorem star4_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T) :
    (star4 f).hom.app T s =
      (starSnd f T s).sdiff (starFst f T s) (star_a_eq f T s).symm :=
  sorry

/-- Union is a morphism over `Y`. -/
theorem star1_comp_finitePartTo {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f] :
    star1 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f :=
  sorry

/-- Intersection is a morphism over `Y`. -/
theorem star2_comp_finitePartTo {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f] :
    star2 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f :=
  sorry

/-- Set-difference is a morphism over `Y`. -/
theorem star3_comp_finitePartTo {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f] :
    star3 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f :=
  sorry

/-- Swapped set-difference is a morphism over `Y`. -/
theorem star4_comp_finitePartTo {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f] :
    star4 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f :=
  sorry

/-- Remark 79.12.5 (6): the zero section of `(X/Y)_fin` over `Y` is `(a, ∅)`. -/
@[stacks 04PI]
def finitePartZero {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (toFppfSheaf S).obj Y ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun y ↦
        FinitePart.Point.empty (OpenSubspace.homOfPointsSection (ULift.down y))
      naturality := sorry }

/-- Components of `finitePartZero` are empty finite-part pairs. -/
theorem finitePartZero_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ) (y : ((toFppfSheaf S).obj Y).obj.obj T) :
    (finitePartZero f).hom.app T y =
      FinitePart.Point.empty (OpenSubspace.homOfPointsSection (ULift.down y)) :=
  sorry

/-- The zero section of `(X/Y)_fin` is a section of the structure map to `Y`. -/
theorem finitePartZero_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    finitePartZero f ≫ finitePartTo f = 𝟙 ((toFppfSheaf S).obj Y) :=
  sorry

/-- Remark 79.12.5 (7): if `f` is finite, the unit section is `(a, T ×_Y X)`. -/
@[stacks 04PI]
def finitePartOne {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] : (toFppfSheaf S).obj Y ⟶ finitePartSheaf f :=
  ObjectProperty.homMk
    { app T := TypeCat.ofHom fun y ↦
        FinitePart.Point.univ (OpenSubspace.homOfPointsSection (ULift.down y))
      naturality := sorry }

/-- Components of `finitePartOne` are full finite-part pairs. -/
theorem finitePartOne_app {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] (T : (Over S)ᵒᵖ) (y : ((toFppfSheaf S).obj Y).obj.obj T) :
    (finitePartOne f).hom.app T y =
      FinitePart.Point.univ (OpenSubspace.homOfPointsSection (ULift.down y)) :=
  sorry

/-- The unit section of `(X/Y)_fin` is a section of the structure map to `Y`. -/
theorem finitePartOne_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] :
    finitePartOne f ≫ finitePartTo f = 𝟙 ((toFppfSheaf S).obj Y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
