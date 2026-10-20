/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Condition

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

/-- If étale base change for `f` holds through degree `q - 1` but fails in degree `q`,
then after two cartesian base changes there is a field-valued point and an
`n`-annihilated abelian étale sheaf for which the canonical degree-`q`
comparison is not an isomorphism. -/
theorem exists_fieldCounterexample {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ)
    {q : ℕ} (hq : 1 ≤ q) (hBC : Holds f n (q - 1)) (hfail : ¬ Holds f n q) :
    ∃ (S' X' Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
      (K : Type u) (_ : Field K)
      (g : Scheme.Spec.obj (Opposite.op (CommRingCat.of K)) ⟶ S')
      (h : Y ⟶ X')
      (e : Y ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of K)))
      (sq₁ : IsPullback p f' f s) (sq₂ : IsPullback h e f' g)
      (F : Sheaf (Scheme.Spec.obj (Opposite.op (CommRingCat.of K))).smallEtaleTopology
        AddCommGrpCat.{u + 1}),
      (n : ℤ) • 𝟙 F = 0 ∧ ¬ IsIso (higherMap f' h e g sq₂ q F) := sorry

/-- If étale base change for `f` holds through degree `q - 1` but fails in degree `q`,
there are two cartesian base changes through an affine integral normal scheme with
algebraically closed function field and a dominant algebraically closed field point,
such that the degree-`q` higher direct image of constant cyclic coefficients of
order dividing `n` is nonzero. -/
theorem exists_normalAffineConstantCounterexample
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
    (hBC : Holds f n (q - 1)) (hfail : ¬ Holds f n q) :
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
        ¬ IsZero ((Derived.higherDirectImage h q).obj
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))) := sorry

/-- If étale base change for `f` holds through degree `q - 1` but fails in degree `q`
and `n` is invertible on the base, there are two cartesian base changes through an
affine integral normal scheme with algebraically closed function field, the second
along its generic-point map, such that the degree-`q` higher direct image of constant
cyclic coefficients of order dividing `n` is nonzero. -/
theorem exists_functionFieldConstantCounterexample
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) {q : ℕ} (hq : 1 ≤ q)
    (hBC : Holds f n (q - 1)) (hfail : ¬ Holds f n q)
    (hn : IsUnit (n : Γ(S, ⊤))) :
    ∃ (S' X' Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
      (_ : IsAffine S') (_ : IsIntegral S') (_ : S'.isNormal)
      (_ : IsAlgClosed S'.functionField)
      (h : Y ⟶ X') (e : Y ⟶ Spec S'.functionField)
      (sq₁ : IsPullback p f' f s)
      (sq₂ : IsPullback h e f' (S'.fromSpecStalk (genericPoint S')))
      (d : ℕ),
      (d : ℤ) ∣ n ∧
        ¬ IsZero ((Derived.higherDirectImage h q).obj
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange

end
