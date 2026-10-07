module

public import ReasLib.FieldTheory.Galois.IntegralClosure
public import ReasLib.RingTheory.Invariant.ResidueField.Profinite
public import ReasLib.RingTheory.Invariant.ResidueField.Orbit
public import ReasLib.RingTheory.LocalRing.Integral

@[expose] public section

/-!
# Residue fields of Galois integral closures

This file specializes the profinite invariant residue-field API to the
integral closure of an integrally closed domain in a possibly infinite Galois
extension of its fraction field.

@stack 0BRK
@stack 09ED
-/

universe u v w

namespace integralClosure.ResidueField

variable {A : Type u} {L : Type w}
variable [CommRing A] [Field L] [Algebra A L]

section Base

variable [IsDomain A] [IsLocalRing A]

/-- The canonical residue-field algebra from the closed point of `A` to a maximal branch of its
integral closure. -/
@[implicit_reducible, stacks 09ED "base-to-branch residue-field algebra"]
noncomputable def algebraOfBase
    (m : Ideal (integralClosure A L)) [m.IsMaximal] :
    Algebra (IsLocalRing.maximalIdeal A).ResidueField m.ResidueField :=
  Ideal.ResidueField.algebraOfLiesOver (IsLocalRing.maximalIdeal A) m

end Base

/-- A residue-field extension attached to a prime of a Galois integral
closure is normal. -/
@[stacks 0BRK "normal residue fields of a Galois integral closure",
  stacks 09ED "Lemma 15.113.4 (1), normal residue extension"]
theorem normal
    {K : Type v} [Field K] [Algebra A K] [IsDomain A] [IsIntegrallyClosed A]
    [IsFractionRing A K] [Algebra K L] [IsScalarTower A K L] [IsGalois K L]
    (p : Ideal A) [p.IsPrime]
    (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver p] :
    -- Local instance justification (defeq pin): normality is evaluated for the residue extension induced by the canonical lying-over map.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    Normal p.ResidueField q.ResidueField := sorry
-- Proof strategy: use `integralClosure.isGaloisGroup` to obtain the canonical invariant Galois
-- action and `integralClosure.continuousSMul` for its discrete continuity, then specialize
-- `Ideal.ResidueField.Invariant.normal_of_profinite` to `Gal(L/K)` and the lying-over pair
-- `(p, q)`.

/-- The decomposition group at a prime of a Galois integral closure surjects onto the
automorphism group of the induced residue-field extension. -/
@[stacks 0BRK "surjective residue action for a Galois integral closure",
  stacks 09ED "Lemma 15.113.4 (2) and (4), surjective decomposition-group action"]
theorem stabilizerHom_surjective
    {K : Type v} [Field K] [Algebra A K] [IsDomain A] [IsIntegrallyClosed A]
    [IsFractionRing A K] [Algebra K L] [IsScalarTower A K L] [IsGalois K L]
    (p : Ideal A) [p.IsPrime]
    (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver p] :
    -- Local instance justification (defeq pin): the action codomain uses the same canonical lying-over residue algebra as stabilizerHom.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    Function.Surjective
      (Ideal.ResidueField.Invariant.stabilizerHom (G := Gal(L/K)) p q) := sorry
-- Proof strategy: install the same canonical Galois invariant action and continuous action as in
-- `normal`, then apply
-- `Ideal.ResidueField.Invariant.stabilizerHom_surjective_of_profinite` with `G := Gal(L/K)`.

/-- Residue-field separability is constant on prime
ideals of a Galois integral closure having the same contraction to the base domain. -/
@[stacks 09ED "Lemma 15.113.4, separability depends only on the contracted prime"]
theorem isSeparable_iff_of_under_eq
    {K : Type v} [Field K] [Algebra A K] [IsDomain A] [IsIntegrallyClosed A]
    [IsFractionRing A K] [Algebra K L] [IsScalarTower A K L] [IsGalois K L]
    (q q' : Ideal (integralClosure A L)) [q.IsPrime] [q'.IsPrime]
    (hunder : q.under A = q'.under A) :
    -- Local instance justification (defeq pin): this equality identifies the second contraction with the base prime of the first branch.
    letI : q'.LiesOver (q.under A) := ⟨hunder⟩
    -- Local instance justification (defeq pin): the first separability predicate uses the canonical residue map from the common contracted prime.
    letI : Algebra (q.under A).ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver (q.under A) q
    -- Local instance justification (defeq pin): the second separability predicate uses the residue map from that same contracted prime.
    letI : Algebra (q.under A).ResidueField q'.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver (q.under A) q'
    Algebra.IsSeparable (q.under A).ResidueField q.ResidueField ↔
      Algebra.IsSeparable (q.under A).ResidueField q'.ResidueField := sorry
-- Proof strategy: obtain `σ : Gal(L/K)` with `σ • q = q'` from
-- `integralClosure.exists_smul_eq_of_under_eq`, install the canonical lying-over instance for
-- `q'` over `q.under A`, and apply
-- `Ideal.ResidueField.Invariant.isSeparable_iff_of_smul_eq`.

/-- Separability of residue fields at maximal branches is independent of the branch over a
fixed base prime. -/
@[stacks 09ED "Lemma 15.113.4, separability is independent of the maximal ideal"]
theorem isSeparable_iff_of_maximal
    {K : Type v} [Field K] [Algebra A K] [IsDomain A] [IsIntegrallyClosed A]
    [IsFractionRing A K] [Algebra K L] [IsScalarTower A K L] [IsGalois K L]
    (p : Ideal A) [p.IsPrime]
    (q q' : Ideal (integralClosure A L)) [q.IsPrime] [q'.IsPrime]
    [q.IsMaximal] [q'.IsMaximal] [q.LiesOver p] [q'.LiesOver p] :
    -- Local instance justification (defeq pin): the first branch is viewed over p through its canonical lying-over residue map.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    -- Local instance justification (defeq pin): the second branch is viewed over the same p through its canonical lying-over residue map.
    letI : Algebra p.ResidueField q'.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q'
    Algebra.IsSeparable p.ResidueField q.ResidueField ↔
      Algebra.IsSeparable p.ResidueField q'.ResidueField := sorry
-- Proof strategy: use `q.over_def p` and `q'.over_def p` to identify the two contractions, apply
-- `isSeparable_iff_of_under_eq`, and transport the locally installed residue-field algebra
-- structures along those contraction equalities.

/-- A separable residue-field extension in a Galois integral closure is Galois. -/
@[stacks 09ED "Lemma 15.113.4 (3), separable residue extension is Galois"]
theorem isGalois_of_separable
    {K : Type v} [Field K] [Algebra A K] [IsDomain A] [IsIntegrallyClosed A]
    [IsFractionRing A K] [Algebra K L] [IsScalarTower A K L] [IsGalois K L]
    (p : Ideal A) [p.IsPrime]
    (q : Ideal (integralClosure A L)) [q.IsPrime] [q.IsMaximal] [q.LiesOver p]
    (hsep :
      -- Local instance justification (defeq pin): the separability hypothesis uses the canonical lying-over residue algebra.
      letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
      Algebra.IsSeparable p.ResidueField q.ResidueField) :
    -- Local instance justification (defeq pin): the Galois conclusion uses the identical residue algebra as the separability hypothesis.
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    IsGalois p.ResidueField q.ResidueField := sorry
-- Proof strategy: install `Ideal.ResidueField.algebraOfLiesOver p q`, take normality from
-- `normal (K := K) p q`, and combine its algebraicity/normality component with the explicit
-- separability hypothesis `hsep` to construct the canonical `IsGalois` instance.

end integralClosure.ResidueField
