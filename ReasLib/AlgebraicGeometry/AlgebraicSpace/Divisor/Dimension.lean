module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Prime
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Irreducible

/-!
# Dimensions of divisors on algebraic spaces

An effective Cartier divisor on an algebraic space has strictly smaller dimension
at each point where the ambient dimension is finite.
On a good integral algebraic space, prime divisors and irreducible components
of effective Cartier divisors have δ-dimension one less than the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An effective Cartier divisor has strictly smaller étale-local dimension at
each point where the ambient algebraic space has finite dimension. -/
theorem IsEffectiveCartierDivisor.dimensionAt_lt
    {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X)
    [IsEffectiveCartierDivisor i] (x : |D|)
    (hfin : dimensionAt (Points.map i x) < ⊤) :
    dimensionAt x < dimensionAt (Points.map i x) :=
  sorry

/-- An integral closed subspace of a decent algebraic space is the support of a
prime divisor if and only if its point-set has coheight one. -/
theorem exists_primeDivisor_support_iff_coheight_eq_one {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (Z : ClosedSubspace X) [IsIntegral Z.X] :
    (∃ P : PrimeDivisor X, P.support = ClosedSubspace.irreducibleClosed Z) ↔
      Order.coheight (ClosedSubspace.irreducibleClosed Z) = 1 := by
  constructor
  · rintro ⟨P, hP⟩
    rw [← hP]
    exact P.coheight_eq_one
  · intro h
    exact ⟨PrimeDivisor.ofSupport X (ClosedSubspace.irreducibleClosed Z) h, rfl⟩

/-- An irreducible component of an effective Cartier divisor on a locally
Noetherian integral algebraic space has coheight one. -/
theorem effectiveCartierComponent_coheight_eq_one {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] [IsIntegral X]
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι]
    (C : IrreducibleCloseds (Points X))
    (hC : C ∈ closedSetIrreducibleComponents ⟨D.pointsSet, D.isClosed_pointsSet⟩) :
    Order.coheight C = 1 :=
  sorry

namespace Hom

/-- An irreducible closed support in a good integral algebraic space has coheight
one exactly when its δ-dimension is one less than the ambient δ-dimension. -/
theorem coheight_eq_one_iff_deltaDimension_eq_sub_one {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (T : IrreducibleCloseds (Points X)) :
    Order.coheight T = 1 ↔
      deltaDimension f δ T = deltaDimension f δ (univIrreducibleClosed X) - 1 :=
  sorry

/-- For an integral closed subspace of a good integral algebraic space, being a
prime-divisor support, having coheight one, and having δ-dimension one less than
the ambient space are equivalent. -/
@[stacks 0EPZ]
theorem primeDivisor_tfae {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (Z : ClosedSubspace X)
    [IsIntegral Z.X] :
    List.TFAE
      [∃ P : PrimeDivisor X, P.support = ClosedSubspace.irreducibleClosed Z,
        Order.coheight (ClosedSubspace.irreducibleClosed Z) = 1,
        deltaDimension f δ (ClosedSubspace.irreducibleClosed Z) =
          deltaDimension f δ (univIrreducibleClosed X) - 1] :=
  sorry

/-- Every irreducible component of an effective Cartier divisor on a good
integral algebraic space has δ-dimension one less than the ambient space. -/
@[stacks 0EPZ]
theorem effectiveCartierComponent_deltaDimension_eq_sub_one {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (D : ClosedSubspace X)
    [IsEffectiveCartierDivisor D.ι] (C : IrreducibleCloseds (Points X))
    (hC : C ∈ closedSetIrreducibleComponents ⟨D.pointsSet, D.isClosed_pointsSet⟩) :
    deltaDimension f δ C = deltaDimension f δ (univIrreducibleClosed X) - 1 :=
  sorry

end Hom

namespace PrimeDivisor

/-- The support of a prime divisor on a good integral algebraic space has
δ-dimension one less than the ambient space. -/
theorem deltaDimension_eq_sub_one {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (P : PrimeDivisor X) :
    Hom.deltaDimension f δ P.support =
      Hom.deltaDimension f δ (univIrreducibleClosed X) - 1 :=
  sorry

end PrimeDivisor

end AlgebraicGeometry.AlgebraicSpace
