module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HodgeChern
import ReasLib.AlgebraicGeometry.ProjectiveSpace.DifferentialFormCohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 50.11.3 (1): on standard projective `n`-space over `A`, the cohomology of
the sheaf of relative `p`-forms vanishes unless `p = q` and `q ≤ n`. -/
@[stacks 0FMI]
#check (AlgebraicGeometry.projectiveSpaceDifferentialFormCohomology_isZero :
    ∀ (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n) (p q : ℕ)
      (hpq : ¬ (p = q ∧ q ≤ n)),
      IsZero
        (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
          (Λ[p] Ω[(ProjectiveSpace.toSpec A n).toShHom]) q))

/- Lemma 50.11.3 (2): for `p ≤ n`, the `p`th cohomology of relative `p`-forms on
standard projective `n`-space over `A` is free of rank one. -/
@[stacks 0FMI]
#check (AlgebraicGeometry.projectiveSpaceDifferentialFormCohomology_freeRankOne :
    ∀ (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p ≤ n),
      CategoryTheory.ModuleCat.freeRankOne A
        (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
          (Λ[p] Ω[(ProjectiveSpace.toSpec A n).toShHom]) p))

/- Lemma 50.11.3: for `0 ≤ p ≤ n`, the distinguished basis vector of
`H^p(ℙⁿ_A, Ω^p)` is the cohomology class of the logarithmic Čech cocycle
`c₁^Hodge(𝒪(1))^p`. -/
@[stacks 0FMI]
#check (AlgebraicGeometry.ProjectiveSpace.hodgeChernPower_basis :
    ∀ (A : Type u) [CommRing A] (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p ≤ n),
      ∃ b : Module.Basis (Fin 1) A (ProjectiveSpace.hodgeCohomology A n p),
        Submodule.span A
            {(b (0 : Fin 1) : ProjectiveSpace.hodgeCohomology A n p)} = ⊤ ∧
          (∀ b' : Module.Basis (Fin 1) A (ProjectiveSpace.hodgeCohomology A n p),
            ∃ u : Aˣ,
              (b' (0 : Fin 1) : ProjectiveSpace.hodgeCohomology A n p) =
                u • (b (0 : Fin 1) : ProjectiveSpace.hodgeCohomology A n p)) ∧
          ((hp0 : p = 0) →
            ProjectiveSpace.hodgeChernPower A n 0 (fun _ => 0) =
              Scheme.DeRham.logarithmicGenerator (ProjectiveSpace.toSpec A n) 0 ⊤
                Fin.elim0) ∧
          ((hpos : 0 < p) →
            ∀ I : Fin (p + 1) → Fin (n + 1),
              ProjectiveSpace.hodgeChernPower A n p I =
                Scheme.DeRham.logarithmicGenerator (ProjectiveSpace.toSpec A n) p
                  (ProjectiveSpace.hodgeChernSupport A n p I)
                  (ProjectiveSpace.hodgeChernTransition A n p
                    (Nat.pos_iff_ne_zero.mp hpos) I)))
