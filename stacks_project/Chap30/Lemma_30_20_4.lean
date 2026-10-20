module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealPower.Quotient
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open AlgebraicGeometry.Scheme

universe u

/- Lemma 30.20.4: for a coherent sheaf on a scheme proper over a Noetherian affine base,
one exponent simultaneously controls kernels and stabilizes quotient-cohomology images,
and the quotient-cohomology inverse system satisfies the Mittag-Leffler condition. -/
@[stacks 02OB] #check (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient.existsStabilization :
  ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [IsNoetherianRing A] (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ),
    ∃ c : ℕ, Hom.IdealPowerCohomology.Quotient.Stabilization I f F p c)

/- Lemma 30.20.4 (1): let `A` be a Noetherian ring, `I ⊂ A` an ideal, `f : X ⟶ Spec A`
proper, and `F` coherent on `X`. Then for every `p` there is some `c` such that
`Ker(H^p(X, F) ⟶ H^p(X, F / I^n F)) ≤ I^(n-c) H^p(X, F)` for all `n ≥ c`. -/
@[stacks 02OB] #check (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient.ker_le :
  ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [IsNoetherianRing A] (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ),
    ∃ c : ℕ, ∀ n, c ≤ n →
      LinearMap.ker (Hom.IdealPowerCohomology.Quotient.toQuotient I f F p n).hom ≤
        Ideal.PowerSubmodule.stage I (Hom.cohomology f F p) (n - c))

/- Lemma 30.20.4 (2): under the same hypotheses, the inverse system
`n ↦ H^p(X, F / I^n F)` satisfies the Mittag-Leffler condition. -/
@[stacks 02OB] #check (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient.isMittagLeffler :
  ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [IsNoetherianRing A] (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ),
    SequentialInverseSystem.IsMittagLeffler (Hom.IdealPowerCohomology.Quotient.tower I f F p))

/- Lemma 30.20.4 (3): under the same hypotheses, some `c` makes
`Im(H^p(F / I^k F) ⟶ H^p(F / I^n F)) = Im(H^p(F) ⟶ H^p(F / I^n F))`
for all `k ≥ n + c`. -/
@[stacks 02OB] #check (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient.image_eq :
  ∀ {A : Type u} [CommRing A] {X : Scheme.{u}}
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    [IsNoetherianRing A] (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (p : ℕ),
    ∃ c : ℕ, ∀ n k (h : n + c ≤ k),
      LinearMap.range
          (Hom.IdealPowerCohomology.Quotient.transition I f F p
            (Nat.le_trans (Nat.le_add_right n c) h)).hom =
        LinearMap.range (Hom.IdealPowerCohomology.Quotient.toQuotient I f F p n).hom)
