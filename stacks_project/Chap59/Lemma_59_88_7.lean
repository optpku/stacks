module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Counterexample
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 59.88.7: with `f : X ⟶ S` and `n` as in Remark 59.88.1, if
`BC(f, n, q - 1)` holds but `BC(f, n, q)` fails for some `q ≥ 1`, then there is a
pair of cartesian squares `X ← X' ← Y` over `S ← S' ← Spec(K)` with `S'` affine
integral normal, function field of `S'` algebraically closed, `K` algebraically
closed, `Spec(K) ⟶ S'` dominant, and some `d ∣ n` such that
`R^q h_*(ℤ/dℤ)` is nonzero. -/
@[stacks 0F08] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.exists_normalAffineConstantCounterexample :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
      (hBC : AlgebraicGeometry.Scheme.Etale.BaseChange.Holds f n (q - 1))
      (hfail : ¬ AlgebraicGeometry.Scheme.Etale.BaseChange.Holds f n q),
    ∃ (S' X' Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
      (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
      (g : Scheme.Spec.obj (Opposite.op (CommRingCat.of K)) ⟶ S') (h : Y ⟶ X')
      (e : Y ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of K)))
      (sq₁ : IsPullback p f' f s)
      (sq₂ : IsPullback h e f' g)
      (_ : IsAffine S') (_ : IsIntegral S') (_ : S'.isNormal)
      (_ : IsAlgClosed S'.functionField)
      (_ : IsDominant g)
      (_ : QuasiCompact g) (_ : QuasiSeparated g)
      (_ : HasSheafify
        (Scheme.Spec.obj (Opposite.op (CommRingCat.of K))).smallEtaleTopology
        AddCommGrpCat.{u + 1})
      (_ : HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u + 1})
      (_ : HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u + 1})
      (_ : HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1})
      (_ : HasInjectiveResolutions
        (Sheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of K))).smallEtaleTopology
          AddCommGrpCat.{u + 1}))
      (_ : HasInjectiveResolutions
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (d : ℕ),
      (d : ℤ) ∣ n ∧
        ¬ IsZero ((AlgebraicGeometry.Scheme.Etale.Derived.higherDirectImage h q).obj
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))))

end
