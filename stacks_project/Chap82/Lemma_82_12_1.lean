module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier
public import stacks_project.Chap72.Definition_72_6_2_Prime
public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension

/-!
# Prime divisors and δ-dimension on good integral algebraic spaces

In the good setup of Situation 82.2.1, an integral closed subspace of an
integral algebraic space is a prime divisor if and only if its point-set has
codimension one, if and only if its δ-dimension is one less than that of the
ambient space. Irreducible components of effective Cartier divisors have the
same dimension drop.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The space of points of an integral algebraic space, as an irreducible closed subset. -/
def univIrreducibleClosed {S : Scheme.{u}} (X : AlgebraicSpace S) [IsIntegral X] :
    IrreducibleCloseds (Points X) where
  carrier := Set.univ
  isIrreducible' := sorry
  isClosed' := isClosed_univ

/-- `univIrreducibleClosed X` is the full space of points of `X`. -/
theorem coe_univIrreducibleClosed {S : Scheme.{u}} (X : AlgebraicSpace S) [IsIntegral X] :
    (univIrreducibleClosed X : Set (Points X)) = Set.univ :=
  sorry

/-- An integral closed subspace of a decent algebraic space is the support of a
prime divisor if and only if its point-set has coheight one. -/
theorem exists_primeDivisor_support_iff_coheight_eq_one {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (Z : ClosedSubspace X) [IsIntegral Z.X] :
    (∃ P : PrimeDivisor X, P.support = ClosedSubspace.irreducibleClosed Z) ↔
      Order.coheight (ClosedSubspace.irreducibleClosed Z) = 1 :=
  sorry

namespace Hom

/-- Lemma 82.12.1 (1): in Situation 82.2.1, if `X / B` is good and `X` is integral,
then for an integral closed subspace `Z ⊂ X` the following are equivalent: `Z` is
a prime divisor, `|Z|` has codimension `1` in `|X|`, and
`dim_δ(Z) = dim_δ(X) - 1`. -/
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

/-- For an integral closed subspace of a good integral algebraic space, coheight
one is equivalent to a one-step drop in `δ`-dimension. -/
theorem coheight_eq_one_iff_deltaDimension_eq_sub_one {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (Z : ClosedSubspace X)
    [IsIntegral Z.X] :
    Order.coheight (ClosedSubspace.irreducibleClosed Z) = 1 ↔
      deltaDimension f δ (ClosedSubspace.irreducibleClosed Z) =
        deltaDimension f δ (univIrreducibleClosed X) - 1 :=
  sorry

/-- Lemma 82.12.1 (2): in Situation 82.2.1, if `X / B` is good and `X` is integral,
then every irreducible component of an effective Cartier divisor on `X` has
`δ`-dimension `dim_δ(X) - 1`. -/
@[stacks 0EPZ]
theorem effectiveCartierComponent_deltaDimension_eq_sub_one {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (D : ClosedSubspace X)
    [IsEffectiveCartierDivisor D.ι] (Z : ClosedSubspace X) [IsIntegral Z.X]
    (hZ : ClosedSubspace.irreducibleClosed Z ∈
      closedSetIrreducibleComponents ⟨D.pointsSet, D.isClosed_pointsSet⟩) :
    deltaDimension f δ (ClosedSubspace.irreducibleClosed Z) =
      deltaDimension f δ (univIrreducibleClosed X) - 1 :=
  sorry

/-- An irreducible component of an effective Cartier divisor on a good integral
algebraic space has coheight one in `|X|`. -/
theorem effectiveCartierComponent_coheight_eq_one {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (D : ClosedSubspace X)
    [IsEffectiveCartierDivisor D.ι] (Z : ClosedSubspace X) [IsIntegral Z.X]
    (hZ : ClosedSubspace.irreducibleClosed Z ∈
      closedSetIrreducibleComponents ⟨D.pointsSet, D.isClosed_pointsSet⟩) :
    Order.coheight (ClosedSubspace.irreducibleClosed Z) = 1 :=
  sorry

end Hom

namespace PrimeDivisor

/-- The support of a prime divisor on a good integral algebraic space has
`δ`-dimension one less than the ambient space. -/
theorem deltaDimension_eq_sub_one {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (P : PrimeDivisor X) :
    Hom.deltaDimension f δ P.support =
      Hom.deltaDimension f δ (univIrreducibleClosed X) - 1 :=
  sorry

end PrimeDivisor

end AlgebraicGeometry.AlgebraicSpace
