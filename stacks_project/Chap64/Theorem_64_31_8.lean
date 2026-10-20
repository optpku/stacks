/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.DeJong
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open scoped PowerSeries.WithPiTopology

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Theorem 64.31.8. Let `k` be a finite field and let `X` be a geometrically irreducible
smooth projective curve over `k`. Then de Jong's conjecture holds for `n ≤ 2`: every
continuous `ρ : etaleFundamentalGroup X.left (arithmeticPoint X xbar) →ₜ*
GL (Fin n) (PowerSeries (ZMod ℓ))` has finite geometric monodromy. -/
@[stacks 03VZ] #check
  (AlgebraicGeometry.SchemeOverField.deJongConjecture_of_le_two :
    ∀ {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
      [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
      [ConnectedSpace (geometricBaseChange X)] {n : ℕ}, n ≤ 2 → deJongConjecture X n)

/- Apply-form of the `n ≤ 2` case: a continuous `GL (Fin n)` power series representation
has finite geometric monodromy. -/
#check (AlgebraicGeometry.SchemeOverField.hasFiniteGeometricMonodromy_of_nat_le_two :
  ∀ {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)] {n : ℕ} (hn : n ≤ 2) {ℓ : ℕ} [Fact ℓ.Prime]
    (xbar : GeometricPoint (geometricBaseChange X)) (ρ : GLPowerSeriesRep X n ℓ xbar),
    HasFiniteGeometricMonodromy ρ)

end AlgebraicGeometry.SchemeOverField
