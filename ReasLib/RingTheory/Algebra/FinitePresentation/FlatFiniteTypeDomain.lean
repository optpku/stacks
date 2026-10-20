module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.FinitePresentation

/-!
# Finite presentation of flat finite-type algebras over domains

A flat finite-type algebra over a domain is finitely presented.
-/

@[expose] public section

universe u v

namespace Algebra.FinitePresentation

/-- A flat finite-type algebra over a domain is finitely presented. -/
theorem ofFlatFiniteTypeDomain
    {R : Type u} [CommRing R] [IsDomain R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [Module.Flat R S] :
    Algebra.FinitePresentation R S := sorry

attribute [instance 100] ofFlatFiniteTypeDomain

end Algebra.FinitePresentation
