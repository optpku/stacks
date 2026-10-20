module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent

/-!
# Étale locality of pseudo-coherent scheme morphisms

Pseudo-coherence of scheme morphisms is étale local on the source and target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.PseudoCoherent

/-- Pseudo-coherence of scheme morphisms is étale local on the source and target. -/
instance isEtaleLocalAtSourceAndTarget :
    AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.PseudoCoherent :
        MorphismProperty AlgebraicGeometry.Scheme.{u}) :=
  sorry

end AlgebraicGeometry.PseudoCoherent
