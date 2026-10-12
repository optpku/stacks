/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent

/-!
# Source-locality of pseudo-coherent morphisms

Pseudo-coherence of scheme morphisms is local at the source for the syntomic precoverage.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.PseudoCoherent

/-- Pseudo-coherence of scheme morphisms is local at the source for the syntomic
precoverage. -/
instance isLocalAtSourceSyntomic :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.PseudoCoherent :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage := sorry

end AlgebraicGeometry.PseudoCoherent
