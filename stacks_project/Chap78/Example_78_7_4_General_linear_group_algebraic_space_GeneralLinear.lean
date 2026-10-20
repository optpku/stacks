/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeneralLinear
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_1_Product

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeneralLinear

#check (ofScheme : (S : Scheme.{u}) → (n : ℕ) → [NeZero n] → AlgebraicSpace S)
#check (space : {S : Scheme.{u}} → AlgebraicSpace S → (n : ℕ) → [NeZero n] → AlgebraicSpace S)
#check (hom : {S : Scheme.{u}} → (B : AlgebraicSpace S) → (n : ℕ) → [NeZero n] → space B n ⟶ B)
#check (asOver : {S : Scheme.{u}} → (B : AlgebraicSpace S) → (n : ℕ) → [NeZero n] → Over B)
#check (ofMatrix : {S : Scheme.{u}} → {B : AlgebraicSpace S} → (n : ℕ) → [NeZero n] →
  {T : Over S} → (t : ofOver T ⟶ B) →
    Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤) →
      (Over.mk t ⟶ asOver B n))
#check (toMatrix : {S : Scheme.{u}} → {B : AlgebraicSpace S} → (n : ℕ) → [NeZero n] →
  {T : Over S} → (t : ofOver T ⟶ B) → (f : Over.mk t ⟶ asOver B n) →
    Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤))
#check (groupSpace : {S : Scheme.{u}} → (B : AlgebraicSpace S) → (n : ℕ) → [NeZero n] →
  GroupAlgebraicSpace B)
#check (homOverMulEquiv : {S : Scheme.{u}} → {B : AlgebraicSpace S} → (n : ℕ) → [NeZero n] →
  {T : Over S} → (t : ofOver T ⟶ B) →
    (Over.mk t ⟶ asOver B n) ≃* Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤))

end AlgebraicGeometry.AlgebraicSpace.GeneralLinear
