/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Dimension
import StacksCheckRecall

/-!
# Prime divisors and δ-dimension on good integral algebraic spaces

The prime-divisor criterion and the dimension of every irreducible component
of an effective Cartier divisor are recorded in the shared divisor dimension API.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Lemma 82.12.1 (1): an integral closed subspace is a prime divisor exactly
when its support has codimension one, equivalently a δ-dimension drop of one. -/
@[stacks 0EPZ] #check (AlgebraicGeometry.AlgebraicSpace.Hom.primeDivisor_tfae :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (Z : ClosedSubspace X) [IsIntegral Z.X],
    List.TFAE
      [∃ P : PrimeDivisor X, P.support = ClosedSubspace.irreducibleClosed Z,
        Order.coheight (ClosedSubspace.irreducibleClosed Z) = 1,
        Hom.deltaDimension f δ (ClosedSubspace.irreducibleClosed Z) =
          Hom.deltaDimension f δ (univIrreducibleClosed X) - 1])

/- Lemma 82.12.1 (2): every irreducible component of an effective Cartier
divisor has δ-dimension one less than the ambient integral space. -/
@[stacks 0EPZ] #check (AlgebraicGeometry.AlgebraicSpace.Hom.effectiveCartierComponent_deltaDimension_eq_sub_one :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] [IsIntegral X] (D : ClosedSubspace X)
    [IsEffectiveCartierDivisor D.ι] (C : IrreducibleCloseds (Points X)),
    C ∈ closedSetIrreducibleComponents ⟨D.pointsSet, D.isClosed_pointsSet⟩ →
      Hom.deltaDimension f δ C = Hom.deltaDimension f δ (univIrreducibleClosed X) - 1)
