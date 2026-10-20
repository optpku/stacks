/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Bimodule.Hom

/-!
# Concrete Relative Internal Hom

The carrier of `Hom_B(N, P)` is wrapped rather than identified definitionally with the raw space
`N →ₗ[Bᵐᵒᵖ] P`.  Its right `A`-action is precomposition with the left action on `N`; keeping that
action on a distinct carrier prevents a scalar-action diamond with postcomposition actions that
may already exist on the raw linear-map space.

The generic categorical owner is `CategoryTheory.Bimod.InternalHom`.  This leaf supplies the
universe-polymorphic concrete presentation used for calculations with algebra modules.
-/

@[expose] public section

noncomputable section

namespace Module.Bimodule

universe i j u v w x y z t

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]

/-- The concrete right-`B`-linear internal Hom, on a carrier distinct from the raw linear-map
space so that its precomposition action is instance-safe. -/
@[stacks 09LN "concrete relative internal Hom carrier"]
def InternalHom
    (B : Type w) [Ring B]
    (N : Type y) [AddCommGroup N] [Module Bᵐᵒᵖ N]
    (P : Type z) [AddCommGroup P] [Module Bᵐᵒᵖ P] :=
  ULift.{0} (N →ₗ[Bᵐᵒᵖ] P)

namespace InternalHom

variable {N : Type y} [AddCommGroup N] [Module Bᵐᵒᵖ N]
variable {P : Type z} [AddCommGroup P] [Module Bᵐᵒᵖ P]

/-- Wrap a right-`B`-linear map as a concrete internal-Hom element. -/
def ofLinearMap (f : N →ₗ[Bᵐᵒᵖ] P) : InternalHom B N P :=
  ⟨f⟩

/-- The underlying right-`B`-linear map of a wrapped internal Hom. -/
def toLinearMap (f : InternalHom B N P) : N →ₗ[Bᵐᵒᵖ] P :=
  f.down

/-- The equivalence between the wrapped internal Hom and its underlying right-linear map space. -/
def equiv : InternalHom B N P ≃ (N →ₗ[Bᵐᵒᵖ] P) :=
  Equiv.ulift

/-- Unwrapping a wrapped right-linear map returns the original map. -/
@[simp]
theorem toLinearMap_ofLinearMap (f : N →ₗ[Bᵐᵒᵖ] P) :
    toLinearMap (ofLinearMap (B := B) f) = f := sorry

/-- Rewrapping the underlying right-linear map returns the original internal-Hom element. -/
@[simp]
theorem ofLinearMap_toLinearMap (f : InternalHom B N P) :
    ofLinearMap (B := B) (toLinearMap f) = f := sorry

/-- The additive group structure transported from right-`B`-linear maps. -/
instance instAddCommGroup : AddCommGroup (InternalHom B N P) :=
  (equiv (B := B) (N := N) (P := P)).addCommGroup

/-- The ground-ring module structure transported from right-`B`-linear maps. -/
instance instModuleBase [Module R P] [IsScalarTower R Bᵐᵒᵖ P] :
    Module R (InternalHom B N P) :=
  (equiv (B := B) (N := N) (P := P)).module R

/-- The wrapped internal Hom is `R`-linearly equivalent to the raw right-linear map space. -/
def linearEquiv [Module R P] [IsScalarTower R Bᵐᵒᵖ P] :
    InternalHom B N P ≃ₗ[R] (N →ₗ[Bᵐᵒᵖ] P) :=
  (equiv (B := B) (N := N) (P := P)).linearEquiv R

/-- Wrapped internal Homs act on their source. -/
instance instCoeFun : CoeFun (InternalHom B N P) (fun _ ↦ N → P) where
  coe f := toLinearMap f

/-- Wrapped internal Homs are determined by their underlying right-linear maps. -/
@[ext]
theorem ext {f g : InternalHom B N P} (h : toLinearMap f = toLinearMap g) : f = g := sorry

/-- Evaluation of a wrapped internal Hom is evaluation of its underlying linear map. -/
@[simp]
theorem coe_apply (f : InternalHom B N P) (n : N) : f n = toLinearMap f n := sorry

section Precomposition

variable [Module A N] [SMulCommClass A Bᵐᵒᵖ N]

/-- Evaluation after precomposition with a left scalar action is additive. -/
theorem precomp_add (a : Aᵐᵒᵖ) (f : InternalHom B N P) (n n' : N) :
    f (MulOpposite.unop a • (n + n')) =
      f (MulOpposite.unop a • n) + f (MulOpposite.unop a • n') := sorry

/-- Evaluation after precomposition with a left scalar action is right-linear. -/
theorem precomp_smul (a : Aᵐᵒᵖ) (f : InternalHom B N P) (b : Bᵐᵒᵖ) (n : N) :
    f (MulOpposite.unop a • (b • n)) = b • f (MulOpposite.unop a • n) := sorry

/-- Precomposition of an internal Hom by a left scalar action. -/
def precomp (a : Aᵐᵒᵖ) (f : InternalHom B N P) : InternalHom B N P :=
  ofLinearMap
    { toFun := fun n ↦ f (MulOpposite.unop a • n)
      map_add' := precomp_add a f
      map_smul' := precomp_smul a f }

/-- Precomposition by the unit scalar fixes an internal Hom. -/
theorem one_smul (f : InternalHom B N P) : precomp (1 : Aᵐᵒᵖ) f = f := sorry

/-- Precomposition by a product agrees with successive precomposition. -/
theorem mul_smul (a a' : Aᵐᵒᵖ) (f : InternalHom B N P) :
    precomp (a * a') f = precomp a (precomp a' f) := sorry

/-- Precomposition preserves the zero internal Hom. -/
theorem smul_zero (a : Aᵐᵒᵖ) : precomp a (0 : InternalHom B N P) = 0 := sorry

/-- Precomposition distributes over addition of internal Homs. -/
theorem smul_add (a : Aᵐᵒᵖ) (f g : InternalHom B N P) :
    precomp a (f + g) = precomp a f + precomp a g := sorry

/-- Precomposition is additive in the scalar. -/
theorem add_smul (a a' : Aᵐᵒᵖ) (f : InternalHom B N P) :
    precomp (a + a') f = precomp a f + precomp a' f := sorry

/-- Precomposition by the zero scalar is zero. -/
theorem zero_smul (f : InternalHom B N P) : precomp (0 : Aᵐᵒᵖ) f = 0 := sorry

/-- The concrete internal Hom carries the canonical right `A`-action by precomposition. -/
instance instModuleRight : Module Aᵐᵒᵖ (InternalHom B N P) where
  smul := precomp
  one_smul := one_smul
  mul_smul := mul_smul
  smul_zero := smul_zero
  smul_add := smul_add
  add_smul := add_smul
  zero_smul := zero_smul

end Precomposition

/-- The ground-ring and precomposition actions on concrete internal Hom form a scalar tower. -/
instance instIsScalarTowerRight [Module R N] [Module A N]
    [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
    [Module R P] [IsScalarTower R Bᵐᵒᵖ P] :
    IsScalarTower R Aᵐᵒᵖ (InternalHom B N P) := sorry

/-- The right `A`-action on concrete internal Hom evaluates by precomposition. -/
@[simp]
theorem smul_apply [Module A N] [SMulCommClass A Bᵐᵒᵖ N]
    (a : A) (f : InternalHom B N P) (n : N) :
    (MulOpposite.op a • f) n = f (a • n) := sorry

variable [Module R N] [Module A N]
variable [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
variable [SMulCommClass A Bᵐᵒᵖ N]
variable [Module R P] [IsScalarTower R Bᵐᵒᵖ P]

variable {N' : Type x} [AddCommGroup N'] [Module R N'] [Module A N'] [Module Bᵐᵒᵖ N']
variable [IsScalarTower R A N'] [IsScalarTower R Bᵐᵒᵖ N'] [SMulCommClass A Bᵐᵒᵖ N']

/-- Precomposition by a bimodule morphism is additive on internal Homs. -/
theorem mapSource_add
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (g h : InternalHom B N' P) :
    ofLinearMap ((toLinearMap (g + h)).comp (Hom.toRightLinearMap f)) =
      ofLinearMap ((toLinearMap g).comp (Hom.toRightLinearMap f)) +
        ofLinearMap ((toLinearMap h).comp (Hom.toRightLinearMap f)) := sorry

/-- Precomposition by a bimodule morphism preserves the right `A`-action on internal Homs. -/
theorem mapSource_smul
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (a : Aᵐᵒᵖ) (g : InternalHom B N' P) :
    ofLinearMap ((toLinearMap (a • g)).comp (Hom.toRightLinearMap f)) =
      a • ofLinearMap ((toLinearMap g).comp (Hom.toRightLinearMap f)) := sorry

/-- Precomposition by a concrete bimodule morphism on internal Homs. -/
def mapSource
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    InternalHom B N' P →ₗ[Aᵐᵒᵖ] InternalHom B N P where
  toFun g := ofLinearMap ((toLinearMap g).comp (Hom.toRightLinearMap f))
  map_add' := mapSource_add f
  map_smul' := mapSource_smul f

/-- Precomposition on concrete internal Hom evaluates by ordinary composition. -/
@[simp]
theorem mapSource_apply
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (g : InternalHom B N' P) (n : N) :
    mapSource (R := R) (A := A) f g n = g (f n) := sorry

/-- Precomposition by the identity is the identity on concrete internal Hom. -/
@[simp]
theorem mapSource_id :
    mapSource (R := R) (A := A) (B := B) (N := N) (N' := N) (P := P)
      (Hom.id (R := R) (A := A) (B := B) (N := N)) = LinearMap.id := sorry

/-- Precomposition reverses composition of concrete bimodule morphisms. -/
theorem mapSource_comp
    {N'' : Type i} [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N''] [SMulCommClass A Bᵐᵒᵖ N'']
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (g : Hom (R := R) (A := A) (B := B) (N := N') (N' := N'')) :
    mapSource (R := R) (A := A) (B := B) (P := P) (Hom.comp g f) =
      (mapSource (R := R) (A := A) (B := B) (P := P) f).comp
        (mapSource (R := R) (A := A) (B := B) (P := P) g) := sorry

variable {Q : Type t} [AddCommGroup Q] [Module R Q] [Module Bᵐᵒᵖ Q]
variable [IsScalarTower R Bᵐᵒᵖ Q]

/-- Postcomposition by a right-linear map is additive on internal Homs. -/
theorem mapTarget_add (h : P →ₗ[Bᵐᵒᵖ] Q) (f g : InternalHom B N P) :
    ofLinearMap (h.comp (toLinearMap (f + g))) =
      ofLinearMap (h.comp (toLinearMap f)) + ofLinearMap (h.comp (toLinearMap g)) := sorry

/-- Postcomposition by a right-linear map preserves the precomposition scalar action. -/
theorem mapTarget_smul (h : P →ₗ[Bᵐᵒᵖ] Q) (a : Aᵐᵒᵖ) (f : InternalHom B N P) :
    ofLinearMap (h.comp (toLinearMap (a • f))) = a • ofLinearMap (h.comp (toLinearMap f)) := sorry

/-- Postcomposition by a right-`B`-linear map on concrete internal Homs. -/
def mapTarget (h : P →ₗ[Bᵐᵒᵖ] Q) :
    InternalHom B N P →ₗ[Aᵐᵒᵖ] InternalHom B N Q where
  toFun f := ofLinearMap (h.comp (toLinearMap f))
  map_add' := mapTarget_add h
  map_smul' := mapTarget_smul h

/-- Postcomposition on concrete internal Hom evaluates by ordinary composition. -/
@[simp]
theorem mapTarget_apply (h : P →ₗ[Bᵐᵒᵖ] Q) (f : InternalHom B N P) (n : N) :
    mapTarget (A := A) h f n = h (f n) := sorry

/-- Postcomposition by the identity is the identity on concrete internal Hom. -/
@[simp]
theorem mapTarget_id :
    mapTarget (A := A) (B := B) (N := N) (P := P) (Q := P)
      (LinearMap.id : P →ₗ[Bᵐᵒᵖ] P) = LinearMap.id := sorry

/-- Successive postcomposition maps on concrete internal Hom compose in the same order. -/
theorem mapTarget_comp {S : Type i} [AddCommGroup S] [Module R S] [Module Bᵐᵒᵖ S]
    [IsScalarTower R Bᵐᵒᵖ S] (h : P →ₗ[Bᵐᵒᵖ] Q) (k : Q →ₗ[Bᵐᵒᵖ] S) :
    mapTarget (A := A) (B := B) (N := N) (P := P) (Q := S) (k.comp h) =
      (mapTarget (A := A) (B := B) (N := N) (P := Q) (Q := S) k).comp
        (mapTarget (A := A) (B := B) (N := N) (P := P) (Q := Q) h) := sorry

/-- Simultaneously precompose in the source and postcompose in the target of concrete internal
Hom. -/
@[stacks 09LN "functoriality of concrete relative internal Hom"]
def map
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (h : P →ₗ[Bᵐᵒᵖ] Q) :
    InternalHom B N' P →ₗ[Aᵐᵒᵖ] InternalHom B N Q :=
  (mapTarget (A := A) (B := B) (N := N) h).comp
    (mapSource (R := R) (A := A) (B := B) (P := P) f)

/-- Simultaneous source and target mapping evaluates by precomposition followed by
postcomposition. -/
@[simp]
theorem map_apply
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (h : P →ₗ[Bᵐᵒᵖ] Q) (g : InternalHom B N' P) (n : N) :
    map (R := R) (A := A) f h g n = h (g (f n)) := sorry

/-- Precomposition in the source and postcomposition in the target commute on concrete
internal Hom. -/
theorem mapTarget_comp_mapSource
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (h : P →ₗ[Bᵐᵒᵖ] Q) :
    (mapTarget (A := A) (B := B) (N := N) h).comp
        (mapSource (R := R) (A := A) (B := B) (P := P) f) =
      (mapSource (R := R) (A := A) (B := B) (P := Q) f).comp
        (mapTarget (A := A) (B := B) (N := N') h) := sorry

/-- Simultaneous identity maps induce the identity on concrete internal Hom. -/
@[simp]
theorem map_id :
    map (R := R) (A := A) (B := B) (N := N) (N' := N) (P := P) (Q := P)
        (Hom.id (R := R) (A := A) (B := B) (N := N))
        (LinearMap.id : P →ₗ[Bᵐᵒᵖ] P) =
      LinearMap.id := sorry

/-- Simultaneous source and target mapping preserves composition, contravariantly in the source
and covariantly in the target. -/
theorem map_comp
    {N'' : Type i} [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N''] [SMulCommClass A Bᵐᵒᵖ N'']
    {S : Type j} [AddCommGroup S] [Module R S] [Module Bᵐᵒᵖ S]
    [IsScalarTower R Bᵐᵒᵖ S]
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (g : Hom (R := R) (A := A) (B := B) (N := N') (N' := N''))
    (h : P →ₗ[Bᵐᵒᵖ] Q) (k : Q →ₗ[Bᵐᵒᵖ] S) :
    map (R := R) (A := A) (B := B) (N := N) (N' := N'') (P := P) (Q := S)
        (Hom.comp g f) (k.comp h) =
      (map (R := R) (A := A) (B := B) (N := N) (N' := N') (P := Q) (Q := S) f k).comp
        (map (R := R) (A := A) (B := B) (N := N') (N' := N'')
          (P := P) (Q := Q) g h) := sorry

end InternalHom

end Module.Bimodule
