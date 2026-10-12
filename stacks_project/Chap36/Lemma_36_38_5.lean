/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 36.38.5: for a quasi-compact, quasi-separated scheme with the resolution property,
the canonical comparison from vector-bundle `K₀` to perfect-derived `K₀` is bijective. -/
@[stacks 0FDJ] #check
  (AlgebraicGeometry.Scheme.VectorBundleK0.toK0_bijective :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (hX : AlgebraicGeometry.Scheme.HasResolutionProperty X),
      Function.Bijective (AlgebraicGeometry.Scheme.VectorBundleK0.toK0 X))
