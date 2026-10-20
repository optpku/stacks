/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Order
public import stacks_project.Chap72.Lemma_72_6_3

/-!
# Order of vanishing of rational units along prime divisors

On a locally Noetherian integral algebraic space, the order of a rational unit
along a prime divisor is the length difference of principal quotients of the
henselian local ring at the generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped nonZeroDivisors

universe u

#check (AlgebraicGeometry.AlgebraicSpace.PrimeDivisor.ord_spec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X]
    (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ)
    (a b : henselianLocalRing X Z.genericPoint),
    a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint) →
    ∀ (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint)),
    PrimeDivisor.functionFieldToHenselianFraction Z (f : RationalFunction X) =
      IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint))
        a ⟨b, hb⟩ →
    Z.ord f =
      ((Ring.ord (henselianLocalRing X Z.genericPoint) a).toNat : ℤ) -
        ((Ring.ord (henselianLocalRing X Z.genericPoint) b).toNat : ℤ))

#check (AlgebraicGeometry.AlgebraicSpace.PrimeDivisor.ord_eq_length :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X]
    (Z : PrimeDivisor X) (f : (RationalFunction X)ˣ)
    (a b : henselianLocalRing X Z.genericPoint),
    a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint) →
    ∀ (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint)),
    PrimeDivisor.functionFieldToHenselianFraction Z (f : RationalFunction X) =
      IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint))
        a ⟨b, hb⟩ →
    Z.ord f =
      ((Module.length (henselianLocalRing X Z.genericPoint)
          (henselianLocalRing X Z.genericPoint ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length (henselianLocalRing X Z.genericPoint)
          (henselianLocalRing X Z.genericPoint ⧸ Ideal.span {b})).toNat : ℤ))
