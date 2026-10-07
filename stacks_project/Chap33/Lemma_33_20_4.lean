module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FiberDimension

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

section

variable {k : Type u} [Field k]
variable {X Y : AlgebraicGeometry.SchemeOverField k} (f : X ⟶ Y)
variable [AlgebraicGeometry.LocallyAlgebraic X] [AlgebraicGeometry.LocallyAlgebraic Y]

/- Lemma 33.20.4 (1): for every `y : Y`, the fibre `X_y` is locally algebraic over the
residue field `κ(y)`. -/
@[stacks 0B2L] #check
  (AlgebraicGeometry.SchemeOverField.instLocallyAlgebraicFiberOverSpecResidueField f :
    ∀ y : Y.left,
      AlgebraicGeometry.LocallyAlgebraic
        (Over.mk (f.left.fiberOverSpecResidueField y).hom))

variable [IrreducibleSpace X.left]

/- Lemma 33.20.4 (2a): if `X` is irreducible and `d = dim(X) - dim(Z)` for the reduced closure
`Z` of `f(X)`, then every local fibre dimension is at least `d`. -/
@[stacks 0B2L] #check
  (AlgebraicGeometry.SchemeOverField.reducedImageClosureDimensionGap_le_fiberDimensionAt f :
    ∀ x : X.left,
      (AlgebraicGeometry.SchemeOverField.reducedImageClosureDimensionGap f : WithBot ℕ∞) ≤
        f.left.fiberDimensionAt x)

/- Lemma 33.20.4 (2b): if `X` is irreducible, the locus where the local fibre dimension equals
`dim(X) - dim(Z)` is open. -/
@[stacks 0B2L] #check
  (AlgebraicGeometry.SchemeOverField.isOpen_fiberDimensionAt_eq_reducedImageClosureDimensionGap f :
    IsOpen {x : X.left |
      f.left.fiberDimensionAt x =
        (AlgebraicGeometry.SchemeOverField.reducedImageClosureDimensionGap f : WithBot ℕ∞)})

/- Lemma 33.20.4 (2c): if `X` is irreducible, the locus where the local fibre dimension equals
`dim(X) - dim(Z)` is dense. -/
@[stacks 0B2L] #check
  (AlgebraicGeometry.SchemeOverField.dense_fiberDimensionAt_eq_reducedImageClosureDimensionGap f :
    Dense {x : X.left |
      f.left.fiberDimensionAt x =
        (AlgebraicGeometry.SchemeOverField.reducedImageClosureDimensionGap f : WithBot ℕ∞)})

/- Lemma 33.20.4 (2d): if `X` is irreducible and the local ring of `Z` at the point above
`f(x)` has dimension at least one, then the local fibre dimension is at most
`dim(X) - dim(Z) + dim(𝒪_{Z, f(x)}) - 1`. -/
@[stacks 0B2L] #check
  (AlgebraicGeometry.SchemeOverField.reducedImageClosureDimensionGap.fiberDimensionAt_le_add_ringKrullDim_sub_one
    f :
    ∀ (x : X.left),
      1 ≤ ringKrullDim
        ((AlgebraicGeometry.Scheme.Hom.reducedImageClosureOver f).left.presheaf.stalk
          (AlgebraicGeometry.Scheme.Hom.asReducedImageClosureOver f x)) →
        f.left.fiberDimensionAt x ≤
          (((AlgebraicGeometry.SchemeOverField.reducedImageClosureDimensionGap f +
            (ringKrullDim
              ((AlgebraicGeometry.Scheme.Hom.reducedImageClosureOver f).left.presheaf.stalk
                (AlgebraicGeometry.Scheme.Hom.asReducedImageClosureOver f x))).unbotD 0 - 1 : ℕ∞) :
                  WithBot ℕ∞)))

/- Lemma 33.20.4 (2e): if `X` is irreducible and the local ring of `Z` at the point above
`f(x)` has dimension one, then the local fibre dimension equals `dim(X) - dim(Z)`. -/
@[stacks 0B2L] #check
  (AlgebraicGeometry.SchemeOverField.reducedImageClosureDimensionGap.fiberDimensionAt_eq_of_ringKrullDim_eq_one
    f :
    ∀ (x : X.left),
      ringKrullDim
        ((AlgebraicGeometry.Scheme.Hom.reducedImageClosureOver f).left.presheaf.stalk
          (AlgebraicGeometry.Scheme.Hom.asReducedImageClosureOver f x)) = 1 →
        f.left.fiberDimensionAt x =
          (AlgebraicGeometry.SchemeOverField.reducedImageClosureDimensionGap f : WithBot ℕ∞))

end

section

variable {k : Type u} [Field k]
variable {X Y : AlgebraicGeometry.SchemeOverField k} (f : X ⟶ Y)
variable [AlgebraicGeometry.LocallyAlgebraic X] [AlgebraicGeometry.LocallyAlgebraic Y]

/- Lemma 33.20.4 (3): for any `x : X` with `y = f(x)`, the local dimension of `X` at `x`
minus the local dimension of `Y` at `y` is at most the local dimension of `X_y` at `x`. -/
@[stacks 0B2L] #check
  (AlgebraicGeometry.SchemeOverField.topologicalKrullDimAt_sub_image_le_fiberDimensionAt f :
    ∀ x : X.left,
      (((topologicalKrullDimAt x).unbotD 0 -
        (topologicalKrullDimAt (f.left x)).unbotD 0 : ℕ∞) : WithBot ℕ∞) ≤
          f.left.fiberDimensionAt x)

end
