/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import stacks_project.Chap59.Remark_59_88_1

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace BaseChangeCondition

/-- Lemma 59.88.7: with `f : X ⟶ S` and `n` as in Remark 59.88.1, if
`BC(f, n, q - 1)` holds but `BC(f, n, q)` fails for some `q ≥ 1`, then there is a
pair of cartesian squares `X ← X' ← Y` over `S ← S' ← Spec(K)` with `S'` affine
integral normal, function field of `S'` algebraically closed, `K` algebraically
closed, `Spec(K) ⟶ S'` dominant, and some `d ∣ n` such that
`R^q h_*(ℤ/dℤ)` is nonzero. -/
@[stacks 0F08]
theorem exists_normalAffineConstantCounterexample
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
    (hfail : ¬ baseChangeCondition f n q invImg baseChangeMap) :
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
        AddCommGrpCat.{u})
      (_ : HasSheafify S'.smallEtaleTopology AddCommGrpCat.{u})
      (_ : HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u})
      (_ : HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u})
      (_ : HasInjectiveResolutions
        (Sheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of K))).smallEtaleTopology
          AddCommGrpCat.{u}))
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
