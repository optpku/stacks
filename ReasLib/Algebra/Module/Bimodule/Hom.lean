/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Bimodule
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of Algebra Bimodules

This file provides a universe-polymorphic concrete morphism space for modules carrying commuting
left and right algebra actions.  The categorical owner remains Mathlib's `Bimod.Hom`; this leaf is
the calculation-level interface used by explicit quotient presentations.
-/

@[expose] public section

noncomputable section

namespace Module.Bimodule

universe u v w x y z t

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]

/-- The `R`-module of morphisms between left-`A`, right-`B` bimodules, represented as
right-`B`-linear maps which also preserve the left action. -/
def homSubmodule
    {N : Type x} [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
    {N' : Type y} [AddCommGroup N'] [Module R N'] [Module A N'] [Module Bᵐᵒᵖ N']
    [IsScalarTower R A N'] [IsScalarTower R Bᵐᵒᵖ N'] : Submodule R (N →ₗ[Bᵐᵒᵖ] N') where
  carrier := {f | ∀ (a : A) (n : N), f (a • n) = a • f n}
  zero_mem' := by
    intro a n
    simp
  add_mem' := by
    intro f g hf hg a n
    change f (a • n) + g (a • n) = a • (f n + g n)
    rw [hf a n, hg a n]
    exact (smul_add a (f n) (g n)).symm
  smul_mem' := by
    intro r f hf a n
    change r • f (a • n) = a • (r • f n)
    calc
      r • f (a • n) = r • (a • f n) := congrArg (fun x => r • x) (hf a n)
      _ = a • (r • f n) := smul_comm r a (f n)

/-- A morphism of left-`A`, right-`B` bimodules in the concrete module presentation. -/
@[stacks 09LN "concrete algebra-bimodule morphisms"]
abbrev Hom
    {N : Type x} [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
    {N' : Type y} [AddCommGroup N'] [Module R N'] [Module A N'] [Module Bᵐᵒᵖ N']
    [IsScalarTower R A N'] [IsScalarTower R Bᵐᵒᵖ N'] :=
  homSubmodule (R := R) (A := A) (B := B) (N := N) (N' := N')

namespace Hom

variable {N : Type x} [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
variable {N' : Type y} [AddCommGroup N'] [Module R N'] [Module A N'] [Module Bᵐᵒᵖ N']
variable [IsScalarTower R A N'] [IsScalarTower R Bᵐᵒᵖ N']

/-- The underlying right-`B`-linear map of a concrete bimodule morphism. -/
def toRightLinearMap (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    N →ₗ[Bᵐᵒᵖ] N' :=
  f.1

/-- The underlying left-`A`-linear map of a concrete bimodule morphism. -/
def toLeftLinearMap (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    N →ₗ[A] N' where
  toFun := toRightLinearMap f
  map_add' := by
    intro x y
    exact (toRightLinearMap f).map_add x y
  map_smul' := by
    intro a n
    change toRightLinearMap f (a • n) = a • toRightLinearMap f n
    exact (show ∀ (a : A) (n : N), toRightLinearMap f (a • n) = a • toRightLinearMap f n from f.2) a n

/-- Concrete bimodule morphisms act on their underlying carriers. -/
instance instCoeFun :
    CoeFun (Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) (fun _ ↦ N → N') where
  coe f := toRightLinearMap f

/-- Evaluation of a concrete bimodule morphism is evaluation of its right-linear map. -/
@[simp]
theorem coe_apply (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) (n : N) :
    f n = toRightLinearMap f n := rfl

/-- A concrete bimodule morphism commutes with the left action. -/
@[simp]
theorem map_left_smul
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) (a : A) (n : N) :
    f (a • n) = a • f n := by
  exact (show ∀ (a : A) (n : N), toRightLinearMap f (a • n) = a • toRightLinearMap f n from f.2) a n

/-- A concrete bimodule morphism commutes with the right action. -/
@[simp]
theorem map_right_smul
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (b : Bᵐᵒᵖ) (n : N) : f (b • n) = b • f n :=
  by
    exact (toRightLinearMap f).map_smul b n

/-- Concrete bimodule morphisms are equal when they agree on every input. -/
@[ext]
theorem ext
    {f g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')}
    (h : ∀ n, f n = g n) : f = g := by
  apply Subtype.ext
  apply LinearMap.ext
  intro n
  exact h n

/-- The identity concrete bimodule morphism. -/
def id [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] :
    Hom (R := R) (A := A) (B := B) (N := N) (N' := N) :=
  ⟨LinearMap.id, by
    change ∀ (a : A) (n : N), LinearMap.id (a • n) = a • LinearMap.id n
    intro a n
    rfl⟩

/-- Composition of concrete bimodule morphisms. -/
def comp
    {N'' : Type z} [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N'']
    (g : Hom (R := R) (A := A) (B := B) (N := N') (N' := N''))
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    Hom (R := R) (A := A) (B := B) (N := N) (N' := N'') :=
  ⟨(toRightLinearMap g).comp (toRightLinearMap f), by
    change ∀ (a : A) (n : N),
      ((toRightLinearMap g).comp (toRightLinearMap f)) (a • n) =
        a • ((toRightLinearMap g).comp (toRightLinearMap f)) n
    intro a n
    change g (f (a • n)) = a • g (f n)
    rw [map_left_smul f, map_left_smul g]
  ⟩

/-- The identity concrete bimodule morphism acts as the identity. -/
@[simp]
theorem id_apply [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] (n : N) :
    id (R := R) (A := A) (B := B) (N := N) n = n := rfl

/-- Composition of concrete bimodule morphisms evaluates by ordinary composition. -/
@[simp]
theorem comp_apply
    {N'' : Type z} [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N'']
    (g : Hom (R := R) (A := A) (B := B) (N := N') (N' := N''))
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) (n : N) :
    comp g f n = g (f n) := rfl

/-- Postcomposition with the identity concrete bimodule morphism changes no morphism. -/
@[simp]
theorem id_comp
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    comp (id (R := R) (A := A) (B := B) (N := N')) f = f := by
  apply ext
  intro n
  rfl

/-- Precomposition with the identity concrete bimodule morphism changes no morphism. -/
@[simp]
theorem comp_id [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    comp f (id (R := R) (A := A) (B := B) (N := N)) = f := by
  apply ext
  intro n
  rfl

/-- Composition of concrete bimodule morphisms is associative. -/
theorem assoc
    {N'' : Type z} [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N'']
    {N''' : Type t} [AddCommGroup N'''] [Module R N'''] [Module A N'''] [Module Bᵐᵒᵖ N''']
    [IsScalarTower R A N'''] [IsScalarTower R Bᵐᵒᵖ N''']
    (h : Hom (R := R) (A := A) (B := B) (N := N'') (N' := N'''))
    (g : Hom (R := R) (A := A) (B := B) (N := N') (N' := N''))
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    comp h (comp g f) = comp (comp h g) f := by
  apply ext
  intro n
  rfl

end Hom

end Module.Bimodule
