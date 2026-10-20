module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Counterexample
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.90.3: with `f : X ⟶ S` and `n` as in Remark 59.88.1, assume `n` is
invertible on `S` and that `BC(f, n, q - 1)` holds but `BC(f, n, q)` fails for
some `q ≥ 1`. Then there is a pair of cartesian squares `X ← X' ← Y` over
`S ← S' ← Spec(K)` with `S'` affine integral normal, `K` the algebraically
closed function field of `S'`, and some `d ∣ n` such that `R^q h_*(ℤ/dℤ)` is
nonzero. -/
@[stacks 0F1D] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.exists_functionFieldConstantCounterexample :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
      (hBC : Scheme.Etale.BaseChange.Holds f n (q - 1))
      (hfail : ¬ Scheme.Etale.BaseChange.Holds f n q)
      (hn : IsUnit (n : Γ(S, ⊤))),
    ∃ (S' X' Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
      (_ : IsAffine S') (_ : IsIntegral S') (_ : S'.isNormal)
      (_ : IsAlgClosed S'.functionField)
      (h : Y ⟶ X') (e : Y ⟶ Spec S'.functionField)
      (sq₁ : IsPullback p f' f s)
      (sq₂ : IsPullback h e f' (S'.fromSpecStalk (genericPoint S')))
      (d : ℕ),
      (d : ℤ) ∣ n ∧
        ¬ IsZero ((Scheme.Etale.Derived.higherDirectImage h q).obj
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))))

end
