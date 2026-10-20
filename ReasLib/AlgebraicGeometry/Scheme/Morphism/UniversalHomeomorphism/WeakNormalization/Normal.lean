module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Normalization

/-!
# Weakly normal schemes

This module defines weak normality in terms of the morphism from a weak normalization to the
original scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

/-- A scheme is weakly normal when every weak-normalization morphism to it is an isomorphism. -/
@[stacks 0H3S]
class WeaklyNormal : Prop where
  /-- The morphism from any weak normalization to the original scheme is an isomorphism. -/
  isIso_toScheme : ∀ W : WeakNormalization X, IsIso W.toScheme

/-- A scheme is weakly normal exactly when every weak-normalization morphism to it is an
isomorphism. -/
theorem weaklyNormal_iff :
    WeaklyNormal X ↔ ∀ W : WeakNormalization X, IsIso W.toScheme := sorry

end AlgebraicGeometry.Scheme
