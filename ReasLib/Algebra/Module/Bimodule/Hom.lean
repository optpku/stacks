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
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

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
  map_add' := sorry
  map_smul' := sorry

/-- Concrete bimodule morphisms act on their underlying carriers. -/
instance instCoeFun :
    CoeFun (Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) (fun _ ↦ N → N') where
  coe f := toRightLinearMap f

/-- Evaluation of a concrete bimodule morphism is evaluation of its right-linear map. -/
@[simp]
theorem coe_apply (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) (n : N) :
    f n = toRightLinearMap f n := sorry

/-- A concrete bimodule morphism commutes with the left action. -/
@[simp]
theorem map_left_smul
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) (a : A) (n : N) :
    f (a • n) = a • f n := sorry

/-- A concrete bimodule morphism commutes with the right action. -/
@[simp]
theorem map_right_smul
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (b : Bᵐᵒᵖ) (n : N) : f (b • n) = b • f n := sorry

/-- Concrete bimodule morphisms are equal when they agree on every input. -/
@[ext]
theorem ext
    {f g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')}
    (h : ∀ n, f n = g n) : f = g := sorry

/-- The identity concrete bimodule morphism. -/
def id [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] :
    Hom (R := R) (A := A) (B := B) (N := N) (N' := N) :=
  ⟨LinearMap.id, sorry⟩

/-- Composition of concrete bimodule morphisms. -/
def comp
    {N'' : Type z} [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N'']
    (g : Hom (R := R) (A := A) (B := B) (N := N') (N' := N''))
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    Hom (R := R) (A := A) (B := B) (N := N) (N' := N'') :=
  ⟨(toRightLinearMap g).comp (toRightLinearMap f), sorry⟩

/-- The identity concrete bimodule morphism acts as the identity. -/
@[simp]
theorem id_apply [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] (n : N) :
    id (R := R) (A := A) (B := B) (N := N) n = n := sorry

/-- Composition of concrete bimodule morphisms evaluates by ordinary composition. -/
@[simp]
theorem comp_apply
    {N'' : Type z} [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N'']
    (g : Hom (R := R) (A := A) (B := B) (N := N') (N' := N''))
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) (n : N) :
    comp g f n = g (f n) := sorry

/-- Postcomposition with the identity concrete bimodule morphism changes no morphism. -/
@[simp]
theorem id_comp
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    comp (id (R := R) (A := A) (B := B) (N := N')) f = f := sorry

/-- Precomposition with the identity concrete bimodule morphism changes no morphism. -/
@[simp]
theorem comp_id [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    comp f (id (R := R) (A := A) (B := B) (N := N)) = f := sorry

/-- Composition of concrete bimodule morphisms is associative. -/
theorem assoc
    {N'' : Type z} [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N'']
    {N''' : Type t} [AddCommGroup N'''] [Module R N'''] [Module A N'''] [Module Bᵐᵒᵖ N''']
    [IsScalarTower R A N'''] [IsScalarTower R Bᵐᵒᵖ N''']
    (h : Hom (R := R) (A := A) (B := B) (N := N'') (N' := N'''))
    (g : Hom (R := R) (A := A) (B := B) (N := N') (N' := N''))
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    comp h (comp g f) = comp (comp h g) f := sorry

end Hom

end Module.Bimodule
