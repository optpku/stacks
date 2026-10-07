module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Factorization
public import ReasLib.CategoryTheory.Functor.MappingPath

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace DottedArrow

variable {B : Type u} [Bicategory.{w, v} B]
variable {T X Y Z : B} {z : T ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z}
variable (sq : Bicategory.PseudoPullbackCone z (f ≫ g))

section FactorRightFunctorImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The upper-left comparison after factoring the right edge of a dotted-arrow square. -/
private def factorRightLeftIso (A : DottedArrow sq) :
    sq.fst ≫ (A.arrow ≫ f) ≅ sq.snd ≫ f :=
  (α_ sq.fst A.arrow f).symm ≪≫ whiskerRightIso A.left f

/-- The lower-right comparison after factoring the right edge of a dotted-arrow square. -/
private def factorRightRightIso (A : DottedArrow sq) :
    z ≅ (A.arrow ≫ f) ≫ g :=
  A.right ≪≫ (α_ A.arrow f g).symm

/-- The factored comparisons satisfy the middle-square coherence.

Proof strategy: unfold factorRightLeftIso and factorRightRightIso, substitute A.comm, and
normalize the remaining associators by bicategorical coherence. -/
private theorem factorRightObj_comm (A : DottedArrow sq) :
    whiskerLeftIso sq.fst (factorRightRightIso sq A) ≪≫
        (α_ sq.fst (A.arrow ≫ f) g).symm ≪≫
          whiskerRightIso (factorRightLeftIso sq A) g =
      (Bicategory.PseudoPullbackCone.factorRight sq).iso := sorry

/-- Factor an outer dotted arrow through the middle object. -/
private def factorRightObj (A : DottedArrow sq) :
    DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq) where
  arrow := A.arrow ≫ f
  left := factorRightLeftIso sq A
  right := factorRightRightIso sq A
  comm := factorRightObj_comm sq A

/-- Left-comparison compatibility for a factored dotted-arrow morphism.

Proof strategy: use η.left_comm and associator naturality for right whiskering by f. -/
private theorem factorRightMap_left_comm {A A' : DottedArrow sq} (η : A ⟶ A') :
    sq.fst ◁ (η.hom ▷ f) ≫ (factorRightObj sq A').left.hom =
      (factorRightObj sq A).left.hom := sorry

/-- Right-comparison compatibility for a factored dotted-arrow morphism.

Proof strategy: use η.right_comm and associator naturality to move right whiskering through the
factorization f ≫ g. -/
private theorem factorRightMap_right_comm {A A' : DottedArrow sq} (η : A ⟶ A') :
    (factorRightObj sq A).right.hom ≫ (η.hom ▷ f) ▷ g =
      (factorRightObj sq A').right.hom := sorry

/-- The factored morphism induced by an outer dotted-arrow morphism. -/
private def factorRightMap {A A' : DottedArrow sq} (η : A ⟶ A') :
    factorRightObj sq A ⟶ factorRightObj sq A' where
  hom := η.hom ▷ f
  left_comm := factorRightMap_left_comm sq η
  right_comm := factorRightMap_right_comm sq η

/-- Factoring the right edge preserves identity dotted-arrow morphisms.

Proof strategy: apply DottedArrow.Hom.ext and use the identity law for right whiskering by f. -/
private theorem factorRightMap_id (A : DottedArrow sq) :
    factorRightMap sq (𝟙 A) = 𝟙 (factorRightObj sq A) := sorry

/-- Factoring the right edge preserves composition of dotted-arrow morphisms.

Proof strategy: apply DottedArrow.Hom.ext and use the composition law for right whiskering by f. -/
private theorem factorRightMap_comp {A A' A'' : DottedArrow sq}
    (η : A ⟶ A') (θ : A' ⟶ A'') :
    factorRightMap sq (η ≫ θ) = factorRightMap sq η ≫ factorRightMap sq θ := sorry

end Implementation

/-- The functor sending an outer dotted arrow to its middle factor. -/
def factorRightFunctor :
    DottedArrow sq ⥤ DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq) where
  obj := Implementation.factorRightObj sq
  map := Implementation.factorRightMap sq
  map_id := Implementation.factorRightMap_id sq
  map_comp := Implementation.factorRightMap_comp sq

end FactorRightFunctorImplementation

/-- The arrow underlying the middle factor of an outer dotted arrow.

Proof strategy: unfold factorRightFunctor and its private object implementation. -/
@[simp] theorem factorRightFunctor.obj.arrow (A : DottedArrow sq) :
    ((factorRightFunctor sq).obj A).arrow = A.arrow ≫ f := sorry

/-- The left comparison of the middle factor of an outer dotted arrow.

Proof strategy: unfold factorRightFunctor and its private object implementation. -/
@[simp] theorem factorRightFunctor.obj.left (A : DottedArrow sq) :
    ((factorRightFunctor sq).obj A).left =
      (α_ sq.fst A.arrow f).symm ≪≫ whiskerRightIso A.left f := sorry

/-- The right comparison of the middle factor of an outer dotted arrow.

Proof strategy: unfold factorRightFunctor and its private object implementation. -/
@[simp] theorem factorRightFunctor.obj.right (A : DottedArrow sq) :
    ((factorRightFunctor sq).obj A).right =
      A.right ≪≫ (α_ A.arrow f g).symm := sorry

/-- The ambient 2-morphism underlying the middle factor of a dotted-arrow morphism.

Proof strategy: unfold factorRightFunctor and its private map implementation. -/
@[simp] theorem factorRightFunctor.map.hom {A A' : DottedArrow sq} (η : A ⟶ A') :
    ((factorRightFunctor sq).map η).hom = η.hom ▷ f := sorry

/-- The mapped ambient cell satisfies the left triangular compatibility after
factoring the right edge. -/
@[simp]
theorem factorRightFunctor.map.leftComm
    {A A' : DottedArrow sq} (η : A ⟶ A') :
    sq.fst ◁ ((factorRightFunctor sq).map η).hom ≫
        ((factorRightFunctor sq).obj A').left.hom =
      ((factorRightFunctor sq).obj A).left.hom := sorry

/-- The mapped ambient cell satisfies the right triangular compatibility after
factoring the right edge. -/
@[simp]
theorem factorRightFunctor.map.rightComm
    {A A' : DottedArrow sq} (η : A ⟶ A') :
    ((factorRightFunctor sq).obj A).right.hom ≫
        ((factorRightFunctor sq).map η).hom ▷ g =
      ((factorRightFunctor sq).obj A').right.hom := sorry

/-- The left square determined by a fixed dotted arrow in the factored middle square

                              sq.snd
                    sq.pt ───────────────────────▶ X
                      │                            │
               sq.fst │                            │ f
                      ▼                            ▼
                      T ─────────────────────────▶ Y
                                  d.arrow

with comparison d.left. -/
def leftFactorSquare
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq)) :
    Bicategory.PseudoPullbackCone d.arrow f where
  pt := sq.pt
  fst := sq.fst
  snd := sq.snd
  iso := d.left

/-- The left factor square retains the apex of the original outer square. -/
@[simp] theorem leftFactorSquare.pt
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq)) :
    (leftFactorSquare sq d).pt = sq.pt := sorry

/-- The left factor square retains the left leg of the original outer square. -/
@[simp] theorem leftFactorSquare.fst
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq)) :
    (leftFactorSquare sq d).fst = sq.fst := sorry

/-- The right leg of the left factor square is the right leg of the original outer square. -/
@[simp] theorem leftFactorSquare.snd
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq)) :
    (leftFactorSquare sq d).snd = sq.snd := sorry

/-- The comparison of the left factor square is the left triangular comparison of its chosen
middle dotted arrow. -/
@[simp] theorem leftFactorSquare.iso
    (d : DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq)) :
    (leftFactorSquare sq d).iso = d.left := sorry

namespace Factorization

/-- The projection from a dotted-arrow factorization to its chosen middle dotted arrow. This is a
transparent projection view of the canonical categorical-mapping-path owner. -/
abbrev projection :
    Functor.MappingPath (factorRightFunctor sq) ⥤
      DottedArrow (Bicategory.PseudoPullbackCone.factorRight sq) :=
  Functor.MappingPath.projection (factorRightFunctor sq)

end Factorization

end DottedArrow

end CategoryTheory
