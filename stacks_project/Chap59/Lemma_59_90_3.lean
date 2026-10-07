module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import stacks_project.Chap59.Remark_59_88_1
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace BaseChangeCondition

/-- Lemma 59.90.3: with `f : X ⟶ S` and `n` as in Remark 59.88.1, assume `n` is
invertible on `S` and that `BC(f, n, q - 1)` holds but `BC(f, n, q)` fails for
some `q ≥ 1`. Then there is a pair of cartesian squares `X ← X' ← Y` over
`S ← S' ← Spec(K)` with `S'` affine integral normal, `K` the algebraically
closed function field of `S'`, and some `d ∣ n` such that `R^q h_*(ℤ/dℤ)` is
nonzero. -/
@[stacks 0F1D]
theorem exists_functionFieldConstantCounterexample
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
    (invImg : ∀ {A B : Scheme.{u}}, (A ⟶ B) →
      Sheaf B.smallEtaleTopology AddCommGrpCat.{u} ⥤
        Sheaf A.smallEtaleTopology AddCommGrpCat.{u})
    (baseChangeMap :
      ∀ {X' Y S' T : Scheme.{u}}
        (p : X' ⟶ X) (f' : X' ⟶ S') (s : S' ⟶ S)
        (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S')
        [QuasiCompact g] [QuasiSeparated g]
        [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
        [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
        [HasInjectiveResolutions
          (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
        [HasInjectiveResolutions
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})],
        IsPullback p f' f s → IsPullback h e f' g →
        (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) → (q : ℕ) →
        (invImg f').obj
            (Sheaf.higherDirectImage (Scheme.smallEtalePullback g) F q) ⟶
          Sheaf.higherDirectImage (Scheme.smallEtalePullback h)
            ((invImg e).obj F) q)
    (hBC : baseChangeCondition f n (q - 1) invImg baseChangeMap)
    (hfail : ¬ baseChangeCondition f n q invImg baseChangeMap)
    (hn : IsUnit (n : Γ(S, ⊤))) :
    ∃ (S' X' Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
      (_ : IsAffine S') (_ : IsIntegral S') (_ : S'.isNormal)
      (_ : IsAlgClosed S'.functionField)
      (h : Y ⟶ X') (e : Y ⟶ Spec S'.functionField)
      (sq₁ : IsPullback p f' f s)
      (sq₂ : IsPullback h e f' (S'.fromSpecStalk (genericPoint S')))
      (_ : HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u})
      (_ : HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u})
      (_ : HasInjectiveResolutions
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))
      (d : ℕ),
      (d : ℤ) ∣ n ∧
        ¬ IsZero
          (Sheaf.higherDirectImage (Scheme.smallEtalePullback h)
            ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
              (AddCommGrpCat.of (ULift.{u} (ZMod d)))) q :
            Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}) := sorry

end BaseChangeCondition

end

end
