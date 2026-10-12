/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/- Theorem 64.31.9. Let `k` be a finite field and let `X` be a geometrically irreducible
smooth projective curve over `k`. If the prime `ℓ` differs from the characteristic of `k`
and `2 * n < ℓ`, every continuous rank-`n` power-series representation has finite geometric
monodromy. Gaitsgory's Theorem 3.5 and Lemma 3.4 combine with de Jong's Theorem 2.17 to
cover all representations. The source's qualification "modulo some unproven things"
refers to the sheaf/trace formalism and geometric Satake in Gaitsgory §§1.4 and 1.6;
these remain proof dependencies. -/
@[stacks 03W0] #check (AlgebraicGeometry.SchemeOverField.deJongConjectureAt_of_prime_gt_two_mul :
  ∀ {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) {n ℓ : ℕ} [Fact ℓ.Prime]
    (hℓk : (ℓ : k) ≠ 0) (hℓ : 2 * n < ℓ),
    deJongConjectureAt X xbar ℓ n)

/- Apply-form of the `2 * n < ℓ` case, with `ℓ` different from the characteristic of `k`:
a continuous `GL (Fin n)` power-series representation has finite geometric monodromy. -/
#check (AlgebraicGeometry.SchemeOverField.hasFiniteGeometricMonodromy_of_prime_gt_two_mul :
  ∀ {k : Type u} [Field k] [Finite k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X)) {n ℓ : ℕ} [Fact ℓ.Prime]
    (hℓk : (ℓ : k) ≠ 0) (hℓ : 2 * n < ℓ) (ρ : GLPowerSeriesRep X n ℓ xbar),
    HasFiniteGeometricMonodromy ρ)

end AlgebraicGeometry.SchemeOverField
