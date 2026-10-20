/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Left
public import ReasLib.Algebra.Category.DifferentialGraded.Endomorphism
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Endomorphism Actions on a Fixed Differential Graded Module

This leaf owns the reusable degreewise form of an action of a cochain differential graded
algebra on a fixed differential graded module.  `ActionOn` is the mathlib-facing specialization
to an actual `CochainComplex`; the raw-family interface is retained for compatibility with
degreewise constructions.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

variable {R : Type u} [CommRing R]

namespace CategoryTheory.CochainComplex

/-- The endomorphism DGA of a cochain complex of `R`-modules, obtained from the canonical
`R`-linear differential graded category of cochain complexes. -/
@[stacks 0FQ3 "endomorphism DGA of a cochain complex"]
def endomorphismDGA (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    CochainDGAlgebra.{u, v} R :=
  @DifferentialGradedCategory.endomorphismDGA R _
    (CochainComplex (ModuleCat.{v} R) ℤ)
    (differentialGradedCategory (ModuleCat.{v} R) R) K

end CategoryTheory.CochainComplex

/-- Degreewise data for a morphism from `A` to the endomorphism differential graded algebra of
the fixed differential graded `R`-module `(M, dM)`.  The `d_sq` field records the condition that
`dM` is genuinely a differential; all remaining fields are the unital multiplicative action and
its compatibility with the differential. -/
@[stacks 0FQ3]
structure EndomorphismDGAHom (A : CochainDGAlgebra R)
    (M : ℤ → ModuleCat.{v} R) (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) where
  /-- The degree-`m` action of `A^m` on the fixed graded module. -/
  map : ∀ m : ℤ, A.X m →ₗ[R] ∀ p : ℤ, M p →ₗ[R] M (m + p)
  /-- The fixed differential squares to zero. -/
  d_sq (n : ℤ) (x : M n) : dM (n + 1) (dM n x) = 0
  /-- The unit of `A` acts by scalar multiplication. -/
  map_one (r : R) (p : ℤ) (x : M p) :
    map 0 (r • A.one) p x = cast (LeftDifferentialGradedModule.zeroActionTarget p) (r • x)
  /-- Multiplication in `A` acts by composition. -/
  map_mul (i j : ℤ) (a : A.X i) (b : A.X j) (p : ℤ) (x : M p) :
    map (i + j) (A.mul i j a b) p x =
      cast (LeftDifferentialGradedModule.mulActionTarget p i j) (map i a (j + p) (map j b p x))
  /-- The action intertwines the differential on `A` with the endomorphism differential. -/
  comm_d (m : ℤ) (a : A.X m) (p : ℤ) (x : M p) :
    dM (m + p) (map m a p x) =
      cast (LeftDifferentialGradedModule.dLeftActionTarget p m) (map (m + 1) (A.d m a) p x) +
        (m.negOnePow : R) •
          cast (LeftDifferentialGradedModule.dRightActionTarget p m) (map m a (p + 1) (dM p x))

namespace EndomorphismDGAHom

variable {A : CochainDGAlgebra R} {M : ℤ → ModuleCat.{v} R}
  {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}

/-- An endomorphism-DGA action evaluates on a homogeneous algebra element and module element. -/
instance : CoeFun (EndomorphismDGAHom A M dM)
    (fun _ ↦ ∀ m : ℤ, A.X m → ∀ p : ℤ, M p → M (m + p)) where
  coe tau := fun m a p x ↦ tau.map m a p x

/-- Coercion to a function is evaluation of the degreewise action. -/
@[simp] theorem coe_apply (tau : EndomorphismDGAHom A M dM)
    (m : ℤ) (a : A.X m) (p : ℤ) (x : M p) :
    tau m a p x = tau.map m a p x := sorry

/-- Endomorphism-DGA actions are determined by their values on homogeneous elements. -/
@[ext] theorem ext {tau₁ tau₂ : EndomorphismDGAHom A M dM}
    (h : ∀ (m : ℤ) (a : A.X m) (p : ℤ) (x : M p), tau₁ m a p x = tau₂ m a p x) :
    tau₁ = tau₂ := sorry

/-- The multiplicativity field, exposed in evaluation form. -/
theorem map_mul_apply (tau : EndomorphismDGAHom A M dM)
    (i j : ℤ) (a : A.X i) (b : A.X j) (p : ℤ) (x : M p) :
    tau (i + j) (A.mul i j a b) p x =
      cast (LeftDifferentialGradedModule.mulActionTarget p i j) (tau i a (j + p) (tau j b p x)) := sorry

/-- Differential compatibility, exposed in evaluation form. -/
theorem comm_d_apply (tau : EndomorphismDGAHom A M dM)
    (m : ℤ) (a : A.X m) (p : ℤ) (x : M p) :
    dM (m + p) (tau m a p x) =
      cast (LeftDifferentialGradedModule.dLeftActionTarget p m) (tau (m + 1) (A.d m a) p x) +
        (m.negOnePow : R) •
          cast (LeftDifferentialGradedModule.dRightActionTarget p m) (tau m a (p + 1) (dM p x)) := sorry

/-- Package an endomorphism-DGA action as a left differential graded module. -/
def toLeftDifferentialGradedModule (tau : EndomorphismDGAHom A M dM) :
    LeftDifferentialGradedModule A where
  X := M
  d := dM
  smul n m :=
    { toFun := fun a ↦ tau.map n a m
      map_add' := sorry
      map_smul' := sorry }
  d_sq := tau.d_sq
  smul_one := tau.map_one
  smul_mul := fun i j p a b x ↦ tau.map_mul i j a b p x
  comm_d := fun i p a x ↦ tau.comm_d i a p x

/-- The module packaged from an action has the prescribed graded pieces. -/
@[simp] theorem toLeftDifferentialGradedModule_X (tau : EndomorphismDGAHom A M dM) (n : ℤ) :
    tau.toLeftDifferentialGradedModule.X n = M n := sorry

/-- The module packaged from an action has the prescribed differential. -/
@[simp] theorem toLeftDifferentialGradedModule_d (tau : EndomorphismDGAHom A M dM) (n : ℤ) :
    tau.toLeftDifferentialGradedModule.d n = dM n := sorry

/-- The module packaged from an action uses the given degreewise action. -/
@[simp] theorem toLeftDifferentialGradedModule_smul (tau : EndomorphismDGAHom A M dM)
    (n m : ℤ) (a : A.X n) (x : M m) :
    tau.toLeftDifferentialGradedModule.smul n m a x = tau n a m x := sorry

end EndomorphismDGAHom

namespace LeftDifferentialGradedModule

/-- A genuine DGA morphism from `A` to the endomorphism DGA of the cochain complex `K`.  This is
the preferred library-facing interface for an action on an already bundled complex. -/
@[stacks 0FQ3 "differential graded action on a cochain complex"]
abbrev ActionOn (A : CochainDGAlgebra.{u, v} R)
    (K : CochainComplex (ModuleCat.{v} R) ℤ) :=
  CochainDGAlgebra.Hom A (CochainComplex.endomorphismDGA K)

namespace ActionOn

variable {A : CochainDGAlgebra.{u, v} R}
  {K : CochainComplex (ModuleCat.{v} R) ℤ}

/-- Evaluating a genuine map to the endomorphism DGA gives its homogeneous action value. -/
def toEndomorphismValue (tau : ActionOn A K)
    (n : ℤ) (a : A.X n) (p : ℤ) (x : K.X p) : K.X (n + p) :=
  (((tau.toCochainMap.f n a : CochainComplex.HomComplex.Cochain K K n).v
      p (n + p) (Int.add_comm p n)).hom) x

/-- Forget a genuine map to the endomorphism DGA to its degreewise action data. -/
def toEndomorphismDGAHom (tau : ActionOn A K) :
    EndomorphismDGAHom A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom) where
  map n :=
    { toFun := fun a p ↦
        { toFun := toEndomorphismValue tau n a p
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  d_sq := sorry
  map_one := sorry
  map_mul := sorry
  comm_d := sorry

/-- The degreewise action underlying a genuine endomorphism-DGA morphism is evaluation of its
homogeneous cochain. -/
@[simp] theorem toEndomorphismDGAHom_apply (tau : ActionOn A K)
    (n : ℤ) (a : A.X n) (p : ℤ) (x : K.X p) :
    tau.toEndomorphismDGAHom n a p x = toEndomorphismValue tau n a p x := sorry

end ActionOn

end LeftDifferentialGradedModule

namespace EndomorphismDGAHom

variable {A : CochainDGAlgebra.{u, v} R}
  {K : CochainComplex (ModuleCat.{v} R) ℤ}

/-- Degree equality used to turn a degreewise action map into a homogeneous endomorphism
cochain. -/
theorem actionCochainTargetEq (n p q : ℤ) (hpq : p + n = q) : n + p = q := sorry

/-- The homogeneous endomorphism cochain determined by degreewise action data. -/
def toActionCochain
    (tau : EndomorphismDGAHom A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom))
    (n : ℤ) (a : A.X n) : CochainComplex.HomComplex.Cochain K K n :=
  CochainComplex.HomComplex.Cochain.mk fun p q hpq ↦
    ModuleCat.ofHom <| ModuleCat.castLinearMap
      (congrArg K.X (actionCochainTargetEq n p q hpq)) (tau.map n a p)

/-- Package degreewise endomorphism action data as a genuine DGA morphism to the endomorphism
DGA of `K`. -/
def toActionOn
    (tau : EndomorphismDGAHom A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom)) :
    LeftDifferentialGradedModule.ActionOn A K where
  map n :=
    { toFun := toActionCochain tau n
      map_add' := sorry
      map_smul' := sorry }
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- Evaluating the packaged genuine DGA morphism recovers the associated homogeneous cochain. -/
@[simp] theorem toActionOn_apply
    (tau : EndomorphismDGAHom A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom))
    (n : ℤ) (a : A.X n) :
    toActionOn tau n a = toActionCochain tau n a := sorry

/-- Degreewise action data on a cochain complex is equivalent to a genuine DGA morphism into its
endomorphism DGA. -/
def equivActionOn (A : CochainDGAlgebra.{u, v} R)
    (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    EndomorphismDGAHom A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom) ≃
      LeftDifferentialGradedModule.ActionOn A K where
  toFun := toActionOn
  invFun := LeftDifferentialGradedModule.ActionOn.toEndomorphismDGAHom
  left_inv := sorry
  right_inv := sorry

end EndomorphismDGAHom

namespace LeftDifferentialGradedModule

/-- A left differential graded `A`-module whose graded pieces and differential are the fixed pair
`(M, dM)`.  This compatibility fiber supports degreewise constructions that have not yet bundled
their underlying data as a `CochainComplex`. -/
structure WithFixedUnderlying (A : CochainDGAlgebra R) (M : ℤ → ModuleCat.{v} R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) where
  /-- The underlying left differential graded module. -/
  toLeftDifferentialGradedModule : LeftDifferentialGradedModule A
  /-- Its graded pieces are the fixed family `M`. -/
  X_eq : toLeftDifferentialGradedModule.X = M
  /-- Its differential is `dM` after transport along `X_eq`. -/
  d_eq : X_eq ▸ toLeftDifferentialGradedModule.d = dM

namespace WithFixedUnderlying

variable {A : CochainDGAlgebra R} {M : ℤ → ModuleCat.{v} R}
  {dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)}

/-- The fixed-underlying fiber coerces to its underlying left differential graded module. -/
instance : CoeOut (WithFixedUnderlying A M dM) (LeftDifferentialGradedModule A) where
  coe N := N.toLeftDifferentialGradedModule

/-- The left action of a fixed-underlying module, transported to the fixed graded pieces. -/
def smul (N : WithFixedUnderlying A M dM) (n m : ℤ) :
    A.X n →ₗ[R] M m →ₗ[R] M (n + m) :=
  N.X_eq ▸ N.toLeftDifferentialGradedModule.smul n m

/-- A fixed-underlying module evaluates on homogeneous algebra and module elements. -/
instance : CoeFun (WithFixedUnderlying A M dM)
    (fun _ ↦ ∀ n m : ℤ, A.X n → M m → M (n + m)) where
  coe N := fun n m a x ↦ N.smul n m a x

/-- Coercion to a function is evaluation of the transported action. -/
@[simp] theorem coe_apply (N : WithFixedUnderlying A M dM)
    (n m : ℤ) (a : A.X n) (x : M m) : N n m a x = N.smul n m a x := sorry

/-- Curry the action of a fixed-underlying module into endomorphism-DGA action data. -/
def toEndomorphismDGAHom (N : WithFixedUnderlying A M dM) :
    EndomorphismDGAHom A M dM where
  map n :=
    { toFun := fun a m ↦ N.smul n m a
      map_add' := sorry
      map_smul' := sorry }
  d_sq := sorry
  map_one := sorry
  map_mul := sorry
  comm_d := sorry

/-- Recovering action data from a fixed-underlying module evaluates by its transported action. -/
@[simp] theorem toEndomorphismDGAHom_apply (N : WithFixedUnderlying A M dM)
    (n : ℤ) (a : A.X n) (m : ℤ) (x : M m) :
    N.toEndomorphismDGAHom n a m x = N n m a x := sorry

/-- Package endomorphism-DGA action data in the fixed-underlying fiber. -/
def ofEndomorphismDGAHom (tau : EndomorphismDGAHom A M dM) :
    WithFixedUnderlying A M dM :=
  ⟨tau.toLeftDifferentialGradedModule, rfl, rfl⟩

/-- Packaging action data and evaluating recovers its original action. -/
@[simp] theorem ofEndomorphismDGAHom_apply (tau : EndomorphismDGAHom A M dM)
    (n m : ℤ) (a : A.X n) (x : M m) :
    ofEndomorphismDGAHom tau n m a x = tau n a m x := sorry

/-- Packaging endomorphism action data and currying again is the identity. -/
@[simp] theorem toEndomorphismDGAHom_ofEndomorphismDGAHom
    (tau : EndomorphismDGAHom A M dM) :
    (ofEndomorphismDGAHom tau).toEndomorphismDGAHom = tau := sorry

/-- Currying a fixed-underlying module action and packaging it again is the identity. -/
@[simp] theorem ofEndomorphismDGAHom_toEndomorphismDGAHom
    (N : WithFixedUnderlying A M dM) :
    ofEndomorphismDGAHom N.toEndomorphismDGAHom = N := sorry

/-- Fixed-underlying left differential graded module structures are equivalent to their
degreewise homogeneous action data. -/
def equivEndomorphismDGAHom (A : CochainDGAlgebra R) (M : ℤ → ModuleCat.{v} R)
    (dM : ∀ n : ℤ, M n →ₗ[R] M (n + 1)) :
    WithFixedUnderlying A M dM ≃ EndomorphismDGAHom A M dM where
  toFun := toEndomorphismDGAHom
  invFun := ofEndomorphismDGAHom
  left_inv := sorry
  right_inv := sorry

/-- Lemma 22.13.1: left differential graded `A`-module structures on a fixed cochain complex `K`
are equivalent to genuine DGA morphisms from `A` to the endomorphism DGA of `K`. -/
@[stacks 0FQ3]
def equivActionOn (A : CochainDGAlgebra.{u, v} R)
    (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    WithFixedUnderlying A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom) ≃
      LeftDifferentialGradedModule.ActionOn A K :=
  (equivEndomorphismDGAHom A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom)).trans
    (EndomorphismDGAHom.equivActionOn A K)

/-- The canonical fixed-complex equivalence sends a module structure to its genuine
endomorphism-DGA morphism. -/
@[simp] theorem equivActionOn_apply
    {A : CochainDGAlgebra.{u, v} R} {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (N : WithFixedUnderlying A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom)) :
    equivActionOn A K N = N.toEndomorphismDGAHom.toActionOn := sorry

/-- The forward map of the fixed-underlying equivalence curries the module action. -/
@[simp] theorem equivEndomorphismDGAHom_apply (N : WithFixedUnderlying A M dM) :
    equivEndomorphismDGAHom A M dM N = N.toEndomorphismDGAHom := sorry

/-- The inverse map of the fixed-underlying equivalence packages endomorphism action data. -/
@[simp] theorem equivEndomorphismDGAHom_symm_apply (tau : EndomorphismDGAHom A M dM) :
    (equivEndomorphismDGAHom A M dM).symm tau = ofEndomorphismDGAHom tau := sorry

/-- Currying fixed-underlying module actions is injective. -/
theorem toEndomorphismDGAHom_injective :
    Function.Injective
      (fun N : WithFixedUnderlying A M dM ↦ N.toEndomorphismDGAHom) := sorry

/-- Fixed-underlying modules are determined by their homogeneous actions. -/
@[ext] theorem ext {N₁ N₂ : WithFixedUnderlying A M dM}
    (h : ∀ (n m : ℤ) (a : A.X n) (x : M m), N₁ n m a x = N₂ n m a x) :
    N₁ = N₂ := sorry

/-- Currying fixed-underlying module actions is bijective. -/
theorem toEndomorphismDGAHom_bijective :
    Function.Bijective
      (fun N : WithFixedUnderlying A M dM ↦ N.toEndomorphismDGAHom) := sorry

end WithFixedUnderlying

/-- Recover the fixed-underlying left differential graded module from its genuine
endomorphism-DGA action on a bundled cochain complex. -/
def ActionOn.toFixed
    {A : CochainDGAlgebra.{u, v} R} {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (rho : ActionOn A K) :
    WithFixedUnderlying A (fun n ↦ K.X n) (fun n ↦ (K.d n (n + 1)).hom) :=
  (WithFixedUnderlying.equivActionOn A K).symm rho

end LeftDifferentialGradedModule
