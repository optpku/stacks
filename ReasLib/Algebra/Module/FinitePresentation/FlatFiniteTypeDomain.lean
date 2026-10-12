/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.Affine
public import ReasLib.Algebra.Module.FinitePresentation.RestrictScalars

/-!
# Finite presentation of finite modules flat over a base domain

A finite module over a finite-type algebra over a domain is finitely presented when it is flat
over the domain.
-/

@[expose] public section

universe u v w

namespace Module.FinitePresentation

/-- A finite module over a finite-type algebra over a domain is finitely presented over the
algebra when it is flat over the domain. -/
theorem ofFiniteFlatFiniteTypeDomain
    (R : Type u) [CommRing R] [IsDomain R]
    {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    {M : Type w} [AddCommMonoid M] [Module S M] [Module.Finite S M]
    [Module R M] [IsScalarTower R S M] [Module.Flat R M] :
    Module.FinitePresentation S M := sorry

end Module.FinitePresentation
