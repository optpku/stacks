/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.LocallyOfFiniteType

/-!
# Fibre dimensions of schemes over a field

This module relates local fibre dimensions to the dimension of the reduced closure of a
morphism's image and to local dimensions on its source and target.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {X Y : SchemeOverField k} (f : X ⟶ Y)

/-- The difference between the dimension of the source and the dimension of the reduced closure
of the image of a morphism of schemes over a field. -/
noncomputable def reducedImageClosureDimensionGap : ℕ∞ :=
  (topologicalKrullDim X.left).unbotD 0 -
    (topologicalKrullDim (Scheme.Hom.reducedImageClosureOver f).left).unbotD 0

/-- A residue-field fibre of a locally algebraic scheme is locally algebraic over the residue
field of the target point. -/
instance instLocallyAlgebraicFiberOverSpecResidueField
    [LocallyAlgebraic X] (y : Y.left) :
    LocallyAlgebraic (Over.mk (f.left.fiberOverSpecResidueField y).hom) := sorry

/-- For an irreducible locally algebraic source, the reduced-image-closure dimension gap is a
lower bound for the local fibre dimension at every source point. -/
theorem reducedImageClosureDimensionGap_le_fiberDimensionAt
    [LocallyAlgebraic X] [LocallyAlgebraic Y] [IrreducibleSpace X.left]
    (x : X.left) :
    (reducedImageClosureDimensionGap f : WithBot ℕ∞) ≤ f.left.fiberDimensionAt x := sorry

/-- For an irreducible locally algebraic source, the locus where local fibre dimension equals
the reduced-image-closure dimension gap is open. -/
theorem isOpen_fiberDimensionAt_eq_reducedImageClosureDimensionGap
    [LocallyAlgebraic X] [LocallyAlgebraic Y] [IrreducibleSpace X.left] :
    IsOpen {x : X.left |
      f.left.fiberDimensionAt x = (reducedImageClosureDimensionGap f : WithBot ℕ∞)} := sorry

/-- For an irreducible locally algebraic source, the locus where local fibre dimension equals
the reduced-image-closure dimension gap is dense. -/
theorem dense_fiberDimensionAt_eq_reducedImageClosureDimensionGap
    [LocallyAlgebraic X] [LocallyAlgebraic Y] [IrreducibleSpace X.left] :
    Dense {x : X.left |
      f.left.fiberDimensionAt x = (reducedImageClosureDimensionGap f : WithBot ℕ∞)} := sorry

namespace reducedImageClosureDimensionGap

/-- At a point whose local ring in the reduced image closure has positive dimension, the local
fibre dimension is at most the image-closure dimension gap plus that dimension minus one. -/
theorem fiberDimensionAt_le_add_ringKrullDim_sub_one
    [LocallyAlgebraic X] [LocallyAlgebraic Y] [IrreducibleSpace X.left]
    (x : X.left)
    (h : 1 ≤ ringKrullDim
      ((Scheme.Hom.reducedImageClosureOver f).left.presheaf.stalk
        (Scheme.Hom.asReducedImageClosureOver f x))) :
    f.left.fiberDimensionAt x ≤
      (((reducedImageClosureDimensionGap f +
        (ringKrullDim
          ((Scheme.Hom.reducedImageClosureOver f).left.presheaf.stalk
            (Scheme.Hom.asReducedImageClosureOver f x))).unbotD 0 - 1 : ℕ∞) : WithBot ℕ∞)) := sorry

/-- If the local ring at the corresponding point of the reduced image closure has dimension
one, then the local fibre dimension equals the reduced-image-closure dimension gap. -/
theorem fiberDimensionAt_eq_of_ringKrullDim_eq_one
    [LocallyAlgebraic X] [LocallyAlgebraic Y] [IrreducibleSpace X.left]
    (x : X.left)
    (h : ringKrullDim
      ((Scheme.Hom.reducedImageClosureOver f).left.presheaf.stalk
        (Scheme.Hom.asReducedImageClosureOver f x)) = 1) :
    f.left.fiberDimensionAt x =
      (reducedImageClosureDimensionGap f : WithBot ℕ∞) := sorry

end reducedImageClosureDimensionGap

/-- For a morphism of locally algebraic schemes over a field, the local source dimension minus
the local target dimension is bounded above by the local fibre dimension. -/
theorem topologicalKrullDimAt_sub_image_le_fiberDimensionAt
    [LocallyAlgebraic X] [LocallyAlgebraic Y] (x : X.left) :
    (((topologicalKrullDimAt x).unbotD 0 -
      (topologicalKrullDimAt (f.left x)).unbotD 0 : ℕ∞) : WithBot ℕ∞) ≤
        f.left.fiberDimensionAt x := sorry

end AlgebraicGeometry.SchemeOverField
