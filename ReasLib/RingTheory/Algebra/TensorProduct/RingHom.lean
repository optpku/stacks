/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ring homomorphisms and tensor-product comparison maps

This module defines the restrictions of a ring homomorphism from `B ⊗[A] C`
to its two factors and its base ring. It also packages spans and commutative
squares of raw ring homomorphisms, together with their explicitly selected
tensor products, inclusions, pure tensors, and canonical comparison maps.
-/

open scoped TensorProduct

universe u v w x

namespace Algebra.TensorProduct.RingHom

section

variable {A : Type u} {B : Type v} {C : Type w} {K : Type x}
variable [CommSemiring A] [CommSemiring B] [CommSemiring C] [Semiring K]
variable [Algebra A B] [Algebra A C]

/-- Restrict a ring homomorphism from a tensor product to its left factor. -/
@[stacks 0GIP "tensor-product left restriction"]
noncomputable def restrictLeft (map : B ⊗[A] C →+* K) : B →+* K :=
  map.comp (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C)

/-- Restrict a ring homomorphism from a tensor product to its right factor. -/
@[stacks 0GIP "tensor-product right restriction"]
noncomputable def restrictRight (map : B ⊗[A] C →+* K) : C →+* K :=
  map.comp (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom

/-- Restrict a ring homomorphism from a tensor product to its base ring. -/
@[stacks 0GIP "tensor-product base restriction"]
noncomputable def restrictBase (map : B ⊗[A] C →+* K) : A →+* K :=
  map.comp (algebraMap A (B ⊗[A] C))

/-- Evaluate the left-factor restriction at an element of the left factor. -/
@[stacks 0GIP "tensor-product left restriction evaluation", simp]
theorem restrictLeft_apply (map : B ⊗[A] C →+* K) (b : B) :
    restrictLeft map b = map (Algebra.TensorProduct.includeLeftRingHom b) := sorry

/-- Evaluate the right-factor restriction at an element of the right factor. -/
@[stacks 0GIP "tensor-product right restriction evaluation", simp]
theorem restrictRight_apply (map : B ⊗[A] C →+* K) (c : C) :
    restrictRight map c =
      map ((Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C) c) := sorry

/-- Evaluate the base-ring restriction at an element of the base ring. -/
@[stacks 0GIP "tensor-product base restriction evaluation", simp]
theorem restrictBase_apply (map : B ⊗[A] C →+* K) (a : A) :
    restrictBase map a = map (algebraMap A (B ⊗[A] C) a) := sorry

/-- The base restriction is the composite through the left factor. -/
@[stacks 0GIP "base restriction through the left factor", simp]
theorem restrictBase_eq_restrictLeft (map : B ⊗[A] C →+* K) :
    restrictBase map = (restrictLeft map).comp (algebraMap A B) := sorry

/-- The base restriction is also the composite through the right factor. -/
@[stacks 0GIP "base restriction through the right factor"]
theorem restrictBase_eq_restrictRight (map : B ⊗[A] C →+* K) :
    restrictBase map = (restrictRight map).comp (algebraMap A C) := sorry

end

section RawSpan

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [CommSemiring X] [CommSemiring Y] [CommSemiring Z]

/-- A span of raw ring homomorphisms. It selects the two algebra structures
needed for their tensor product without registering either globally. -/
@[stacks 0GIP "raw ring-homomorphism span"]
structure Span where
  /-- The left leg of the span. -/
  left : X →+* Y
  /-- The right leg of the span. -/
  right : X →+* Z

namespace Span

/-- The `X`-algebra structure on the left target selected by a ring span. -/
@[stacks 0GIP "left algebra selected by a raw span", reducible]
noncomputable def leftAlgebra
    (span : Span (X := X) (Y := Y) (Z := Z)) : Algebra X Y :=
  span.left.toAlgebra

/-- The `X`-algebra structure on the right target selected by a ring span. -/
@[stacks 0GIP "right algebra selected by a raw span", reducible]
noncomputable def rightAlgebra
    (span : Span (X := X) (Y := Y) (Z := Z)) : Algebra X Z :=
  span.right.toAlgebra

/-- The tensor product selected by a span of raw ring homomorphisms. -/
@[stacks 0GIP "tensor product selected by a raw span"]
noncomputable abbrev tensor
    (span : Span (X := X) (Y := Y) (Z := Z)) : Type _ :=
  -- Local instance justification (instance diamond): the explicit span,
  -- rather than the carriers, selects the left algebra structure.
  letI : Algebra X Y := span.leftAlgebra
  -- Local instance justification (instance diamond): the explicit span,
  -- rather than the carriers, selects the right algebra structure.
  letI : Algebra X Z := span.rightAlgebra
  Y ⊗[X] Z

/-- The left inclusion into the tensor product selected by a ring span. -/
@[stacks 0GIP "left inclusion selected by a raw span"]
noncomputable def includeLeft
    (span : Span (X := X) (Y := Y) (Z := Z)) : Y →+* span.tensor :=
  -- Local instance justification (instance diamond): the explicit span selects
  -- the left algebra structure used by its tensor-product carrier.
  letI : Algebra X Y := span.leftAlgebra
  -- Local instance justification (instance diamond): the explicit span selects
  -- the right algebra structure used by its tensor-product carrier.
  letI : Algebra X Z := span.rightAlgebra
  (Algebra.TensorProduct.includeLeft : Y →ₐ[X] Y ⊗[X] Z).toRingHom

/-- The right inclusion into the tensor product selected by a ring span. -/
@[stacks 0GIP "right inclusion selected by a raw span"]
noncomputable def includeRight
    (span : Span (X := X) (Y := Y) (Z := Z)) : Z →+* span.tensor :=
  -- Local instance justification (instance diamond): the explicit span selects
  -- the left algebra structure used by its tensor-product carrier.
  letI : Algebra X Y := span.leftAlgebra
  -- Local instance justification (instance diamond): the explicit span selects
  -- the right algebra structure used by its tensor-product carrier.
  letI : Algebra X Z := span.rightAlgebra
  (Algebra.TensorProduct.includeRight : Z →ₐ[X] Y ⊗[X] Z).toRingHom

/-- A pure tensor in the tensor product selected by a ring span. -/
@[stacks 0GIP "pure tensor selected by a raw span"]
noncomputable def tmul
    (span : Span (X := X) (Y := Y) (Z := Z)) (y : Y) (z : Z) : span.tensor :=
  -- Local instance justification (instance diamond): the explicit span selects
  -- the left algebra structure used by its tensor-product carrier.
  letI : Algebra X Y := span.leftAlgebra
  -- Local instance justification (instance diamond): the explicit span selects
  -- the right algebra structure used by its tensor-product carrier.
  letI : Algebra X Z := span.rightAlgebra
  y ⊗ₜ[X] z

/-- The left inclusion selected by a ring span sends `y` to `y ⊗ₜ 1`. -/
@[stacks 0GIP "left span inclusion evaluation", simp]
theorem includeLeft_apply (span : Span (X := X) (Y := Y) (Z := Z)) (y : Y) :
    span.includeLeft y = span.tmul y 1 := sorry

/-- The right inclusion selected by a ring span sends `z` to `1 ⊗ₜ z`. -/
@[stacks 0GIP "right span inclusion evaluation", simp]
theorem includeRight_apply (span : Span (X := X) (Y := Y) (Z := Z)) (z : Z) :
    span.includeRight z = span.tmul 1 z := sorry

end Span

end RawSpan

section RawSquare

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type x}
variable [CommSemiring X] [CommSemiring Y] [CommSemiring Z] [CommSemiring W]

/-- A commutative square of raw ring homomorphisms.  It is deliberately
independent of any chosen algebra structures, local rings, or prime ideals. -/
@[stacks 0GIP "raw tensor-product comparison square"]
structure Square where
  /-- The upper-left edge. -/
  sourceLeft : X →+* Y
  /-- The upper-right edge. -/
  sourceRight : X →+* Z
  /-- The lower-left edge. -/
  leftTarget : Y →+* W
  /-- The lower-right edge. -/
  rightTarget : Z →+* W
  /-- The two routes from the source to the target agree. -/
  comm : leftTarget.comp sourceLeft = rightTarget.comp sourceRight

namespace Square

/-- Forget the lower edges of a commutative square, retaining its upper span. -/
@[stacks 0GIP "upper span of a raw square"]
def span (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) :
    Span (X := X) (Y := Y) (Z := Z) where
  left := square.sourceLeft
  right := square.sourceRight

/-- The diagonal raw map, defined by the left route of a commutative square. -/
@[stacks 0GIP "diagonal map of a raw square"]
def diagonal
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) : X →+* W :=
  square.leftTarget.comp square.sourceLeft

/-- The diagonal raw map can equivalently be computed through the right route. -/
@[stacks 0GIP "right factorization of a raw square diagonal"]
theorem diagonal_eq_right
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) :
    square.diagonal = square.rightTarget.comp square.sourceRight := sorry

/-- The `X`-algebra structure on the left upper target induced by the
upper-left edge.  This is a named non-instance because different squares can
induce different structures on the same carrier. -/
@[stacks 0GIP "left algebra selected by a raw square", reducible]
noncomputable def leftAlgebra
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) : Algebra X Y :=
  square.span.leftAlgebra

/-- The `X`-algebra structure on the right upper target induced by the
upper-right edge.  It remains square-local rather than a global instance. -/
@[stacks 0GIP "right algebra selected by a raw square", reducible]
noncomputable def rightAlgebra
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) : Algebra X Z :=
  square.span.rightAlgebra

/-- The `X`-algebra structure on the lower target induced by the diagonal
raw map of the square. -/
@[stacks 0GIP "target algebra selected by a raw square", reducible]
noncomputable def targetAlgebra
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) : Algebra X W :=
  square.diagonal.toAlgebra

/-- The tensor product of the upper targets over the algebra structures
selected by a raw commutative square. -/
@[stacks 0GIP "tensor product selected by a raw square"]
noncomputable abbrev tensor
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) : Type _ :=
  square.span.tensor

/-- The left inclusion into the tensor product selected by a raw square. -/
@[stacks 0GIP "left inclusion selected by a raw square"]
noncomputable def includeLeft
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) :
    Y →+* square.tensor :=
  square.span.includeLeft

/-- The right inclusion into the tensor product selected by a raw square. -/
@[stacks 0GIP "right inclusion selected by a raw square"]
noncomputable def includeRight
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) :
    Z →+* square.tensor :=
  square.span.includeRight

/-- The pure tensor in the tensor product selected by a raw square. -/
@[stacks 0GIP "pure tensor selected by a raw square"]
noncomputable def tmul
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W))
    (y : Y) (z : Z) : square.tensor :=
  square.span.tmul y z

end Square

end RawSquare

section RingSquare

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type x}
variable [CommRing X] [CommRing Y] [CommRing Z] [CommRing W]

namespace Square

/-- The tensor-product map induced by a commutative square of rings.  It is
Mathlib's explicit pushout descent map in `CommRingCat`. -/
@[stacks 0GIP "raw tensor-product comparison map"]
noncomputable def map
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) :
    square.tensor →+* W :=
  -- Local instance justification (instance diamond): Mathlib's explicit tensor-product
  -- pushout needs the left algebra structure selected by this particular square.
  letI : Algebra X Y := square.leftAlgebra
  -- Local instance justification (instance diamond): Mathlib's explicit tensor-product
  -- pushout needs the right algebra structure selected by this particular square.
  letI : Algebra X Z := square.rightAlgebra
  -- Local instance justification (defeq pin): Mathlib's pushout theorem is universe-uniform;
  -- this canonical left ULift structure transports the square to one common universe.
  letI : Algebra (ULift.{max u v w x} X) (ULift.{max u v w x} Y) :=
    ULift.algebra' X (ULift.{max u v w x} Y)
  -- Local instance justification (defeq pin): Mathlib's pushout theorem is universe-uniform;
  -- this canonical right ULift structure transports the square to one common universe.
  letI : Algebra (ULift.{max u v w x} X) (ULift.{max u v w x} Z) :=
    ULift.algebra' X (ULift.{max u v w x} Z)
  ULift.ringEquiv.toRingHom.comp <|
    (((CommRingCat.pushoutCoconeIsColimit
      (ULift.{max u v w x} X) (ULift.{max u v w x} Y) (ULift.{max u v w x} Z)).desc
        (CategoryTheory.Limits.PushoutCocone.mk
          (CommRingCat.ofHom square.leftTarget.ulift.{max u v w x, max u v w x})
          (CommRingCat.ofHom square.rightTarget.ulift.{max u v w x, max u v w x})
          (CommRingCat.hom_ext
            (congrArg (RingHom.ulift.{max u v w x, max u v w x}) square.comm)))).hom.comp
      ((Algebra.TensorProduct.uliftEquiv.{max u v w x, max u v w x,
          max u v w x, max u v w x} X X Y Z).toRingHom.comp
        ULift.ringEquiv.symm.toRingHom))

/-- The tensor map of a raw square evaluates a pure tensor by multiplying the
two lower-edge images. -/
@[stacks 0GIP "raw square tensor map on pure tensors", simp]
theorem map_tmul
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W))
    (y : Y) (z : Z) :
    square.map (square.tmul y z) = square.leftTarget y * square.rightTarget z := sorry

/-- The tensor map of a raw square restricts along the left inclusion to the
lower-left edge. -/
@[stacks 0GIP "raw square tensor map left restriction", simp]
theorem map_comp_includeLeft
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) :
    square.map.comp square.includeLeft = square.leftTarget := sorry

/-- The tensor map of a raw square restricts along the right inclusion to the
lower-right edge. -/
@[stacks 0GIP "raw square tensor map right restriction", simp]
theorem map_comp_includeRight
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W)) :
    square.map.comp square.includeRight = square.rightTarget := sorry

/-- Promote the tensor map of a raw square to a ring equivalence once its
bijectivity is available. -/
@[stacks 0GIP "raw tensor-product comparison equivalence"]
noncomputable def equiv
    (square : Square (X := X) (Y := Y) (Z := Z) (W := W))
    (h : Function.Bijective square.map) : square.tensor ≃+* W :=
  RingEquiv.ofBijective square.map h

end Square

end RingSquare

end Algebra.TensorProduct.RingHom
