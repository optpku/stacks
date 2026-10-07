module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Affineness from the global-sections morphism

A scheme is affine when its canonical morphism to the spectrum of its global
sections is a split monomorphism.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme whose canonical morphism to the spectrum of its global sections is
a split monomorphism is affine. -/
@[instance]
theorem isAffine_of_isSplitMono_toSpecΓ (X : Scheme.{u})
    [CategoryTheory.IsSplitMono X.toSpecΓ] : AlgebraicGeometry.IsAffine X := sorry

end AlgebraicGeometry.Scheme
