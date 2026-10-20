module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Counterexample
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 59.88.6: if `Holds f n (q - 1)` but not `Holds f n q` for `1 ≤ q`,
then a field-valued cartesian base change and an `n`-annihilated abelian étale
sheaf witness failure of the canonical degree-`q` base-change comparison. -/
@[stacks 0F07] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.exists_fieldCounterexample :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ}
      (hq : 1 ≤ q) (hBC : AlgebraicGeometry.Scheme.Etale.BaseChange.Holds f n (q - 1))
      (hfail : ¬ AlgebraicGeometry.Scheme.Etale.BaseChange.Holds f n q),
      ∃ (S' X' Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
        (K : Type u) (_ : Field K)
        (g : Scheme.Spec.obj (Opposite.op (CommRingCat.of K)) ⟶ S')
        (h : Y ⟶ X')
        (e : Y ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of K)))
        (sq₁ : IsPullback p f' f s) (sq₂ : IsPullback h e f' g)
        (F : Sheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of K))).smallEtaleTopology
          AddCommGrpCat.{u + 1}),
        (n : ℤ) • 𝟙 F = 0 ∧
          ¬ IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap f' h e g sq₂ q F))

end
