module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Algebra
import StacksCheckRecall

/-! # Finite-part sheaves as algebras over the base -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.FinitePart

universe u

/- Remark 79.12.5
The finite-part sheaf of a separated morphism is a non-unital algebra over the
field with two elements, with symmetric difference as addition and intersection
as multiplication, compatibly with restriction. -/
@[stacks 04PI] #check (AlgebraicGeometry.AlgebraicSpace.finitePartAlgebraLaws :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f],
    ∀ (T : Over S) (a : ofOver T ⟶ Y),
      (∀ (p q r : Fiber f a),
        Fiber.add (Fiber.add p q) r = Fiber.add p (Fiber.add q r) ∧
        Fiber.add p q = Fiber.add q p ∧
        Fiber.add (Fiber.zero f a) p = p ∧
        Fiber.add p (Fiber.zero f a) = p ∧
        Fiber.add p p = Fiber.zero f a ∧
        Fiber.mul (Fiber.mul p q) r = Fiber.mul p (Fiber.mul q r) ∧
        Fiber.mul p q = Fiber.mul q p ∧
        Fiber.mul (Fiber.zero f a) p = Fiber.zero f a ∧
        Fiber.mul p (Fiber.zero f a) = Fiber.zero f a ∧
        Fiber.mul p (Fiber.add q r) = Fiber.add (Fiber.mul p q) (Fiber.mul p r) ∧
        Fiber.mul (Fiber.add p q) r = Fiber.add (Fiber.mul p r) (Fiber.mul q r) ∧
        Fiber.mul p p = p ∧
        Fiber.add p q = Fiber.union (Fiber.sdiff p q) (Fiber.sdiff q p)) ∧
      (∀ (c d : ZMod 2) (p q : Fiber f a),
        Fiber.smul 1 p = p ∧
        Fiber.smul 0 p = Fiber.zero f a ∧
        Fiber.smul c (Fiber.zero f a) = Fiber.zero f a ∧
        Fiber.smul (c * d) p = Fiber.smul c (Fiber.smul d p) ∧
        Fiber.smul (c + d) p = Fiber.add (Fiber.smul c p) (Fiber.smul d p) ∧
        Fiber.smul c (Fiber.add p q) = Fiber.add (Fiber.smul c p) (Fiber.smul c q) ∧
        Fiber.smul c (Fiber.mul p q) = Fiber.mul (Fiber.smul c p) q ∧
        Fiber.smul c (Fiber.mul p q) = Fiber.mul p (Fiber.smul c q)) ∧
      (∀ (T' : Over S) (h : T' ⟶ T) (p q : Fiber f a) (c : ZMod 2),
        Fiber.restrict (Fiber.zero f a) h = Fiber.zero f (ofOverMap h ≫ a) ∧
        Fiber.restrict (Fiber.add p q) h =
          Fiber.add (Fiber.restrict p h) (Fiber.restrict q h) ∧
        Fiber.restrict (Fiber.mul p q) h =
          Fiber.mul (Fiber.restrict p h) (Fiber.restrict q h) ∧
        Fiber.restrict (Fiber.smul c p) h = Fiber.smul c (Fiber.restrict p h)))

#check (AlgebraicGeometry.AlgebraicSpace.finitePartTo :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    finitePartSheaf f ⟶ (toFppfSheaf S).obj Y)

#check (AlgebraicGeometry.AlgebraicSpace.starFst :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T),
    FinitePart.Point f T.unop)

#check (AlgebraicGeometry.AlgebraicSpace.starSnd :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T),
    FinitePart.Point f T.unop)

#check (AlgebraicGeometry.AlgebraicSpace.star_a_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T),
    (starFst f T s).a = (starSnd f T s).a)

#check (AlgebraicGeometry.AlgebraicSpace.star1 :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
    (pullback (finitePartTo f) (finitePartTo f)) ⟶ finitePartSheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.star1_app :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T),
    (star1 f).hom.app T s =
      (starFst f T s).union (starSnd f T s) (star_a_eq f T s))

#check (AlgebraicGeometry.AlgebraicSpace.star1_comp_finitePartTo :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
    star1 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f)

#check (AlgebraicGeometry.AlgebraicSpace.star2 :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
    (pullback (finitePartTo f) (finitePartTo f)) ⟶ finitePartSheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.star2_app :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T),
    (star2 f).hom.app T s =
      (starFst f T s).inter (starSnd f T s) (star_a_eq f T s))

#check (AlgebraicGeometry.AlgebraicSpace.star2_comp_finitePartTo :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
    star2 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f)

#check (AlgebraicGeometry.AlgebraicSpace.star3 :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
    (pullback (finitePartTo f) (finitePartTo f)) ⟶ finitePartSheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.star3_app :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T),
    (star3 f).hom.app T s =
      (starFst f T s).sdiff (starSnd f T s) (star_a_eq f T s))

#check (AlgebraicGeometry.AlgebraicSpace.star3_comp_finitePartTo :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
    star3 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f)

#check (AlgebraicGeometry.AlgebraicSpace.star4 :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
    (pullback (finitePartTo f) (finitePartTo f)) ⟶ finitePartSheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.star4_app :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T),
    (star4 f).hom.app T s =
      (starSnd f T s).sdiff (starFst f T s) (star_a_eq f T s).symm)

#check (AlgebraicGeometry.AlgebraicSpace.star4_comp_finitePartTo :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
    star4 f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartAdd :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
    (pullback (finitePartTo f) (finitePartTo f)) ⟶ finitePartSheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartAdd_app :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] (T : (Over S)ᵒᵖ)
    (s : (pullback (finitePartTo f) (finitePartTo f)).obj.obj T),
    (finitePartAdd f).hom.app T s =
      (starFst f T s).add (starSnd f T s) (star_a_eq f T s))

#check (AlgebraicGeometry.AlgebraicSpace.finitePartAdd_comp_finitePartTo :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f],
    finitePartAdd f ≫ finitePartTo f =
      pullback.fst (finitePartTo f) (finitePartTo f) ≫ finitePartTo f)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartZero :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (toFppfSheaf S).obj Y ⟶ finitePartSheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartZero_app :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : (Over S)ᵒᵖ) (y : ((toFppfSheaf S).obj Y).obj.obj T),
    (finitePartZero f).hom.app T y = FinitePart.Point.empty (yonedaEquiv.symm (ULift.down y)))

#check (AlgebraicGeometry.AlgebraicSpace.finitePartZero_comp :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    finitePartZero f ≫ finitePartTo f = 𝟙 ((toFppfSheaf S).obj Y))

#check (AlgebraicGeometry.AlgebraicSpace.finitePartOne :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f],
    (toFppfSheaf S).obj Y ⟶ finitePartSheaf f)

#check (AlgebraicGeometry.AlgebraicSpace.finitePartOne_app :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    (T : (Over S)ᵒᵖ) (y : ((toFppfSheaf S).obj Y).obj.obj T),
    (finitePartOne f).hom.app T y = FinitePart.Point.univ (yonedaEquiv.symm (ULift.down y)))

#check (AlgebraicGeometry.AlgebraicSpace.finitePartOne_comp :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f],
    finitePartOne f ≫ finitePartTo f = 𝟙 ((toFppfSheaf S).obj Y))

#check (AlgebraicGeometry.AlgebraicSpace.finitePartUnitLaws :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Separated f] [IsFinite f],
    ∀ (T : Over S) (a : ofOver T ⟶ Y),
      (∀ (p q : Fiber f a),
        Fiber.mul (Fiber.one f a) p = p ∧
        Fiber.mul p (Fiber.one f a) = p ∧
        Fiber.sdiff p q = Fiber.mul p (Fiber.add (Fiber.one f a) q) ∧
        Fiber.sdiff q p = Fiber.mul (Fiber.add (Fiber.one f a) p) q) ∧
      (∀ (T' : Over S) (h : T' ⟶ T),
        Fiber.restrict (Fiber.one f a) h = Fiber.one f (ofOverMap h ≫ a)))
