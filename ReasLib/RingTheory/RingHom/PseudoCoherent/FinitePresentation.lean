module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Module
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Basic

/-!
# Finite presentation of pseudo-coherent ring maps

Pseudo-coherent homomorphisms of commutative rings are finitely presented.
-/

@[expose] public section

universe u v

namespace RingHom.IsPseudoCoherentRingMap

/-- A pseudo-coherent homomorphism of commutative rings is of finite presentation. -/
theorem finitePresentation {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (h : f.IsPseudoCoherentRingMap) : f.FinitePresentation := sorry

end RingHom.IsPseudoCoherentRingMap
