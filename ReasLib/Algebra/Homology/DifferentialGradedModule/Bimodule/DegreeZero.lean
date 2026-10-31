/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.Algebra.Category.ModuleCat.TensorProduct
public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule

/-!
# Ordinary Bimodules as Differential Graded Bimodules

An ordinary left-`A`, right-`B` bimodule is a left module over `A ⊗[R] Bᵐᵒᵖ`.  This file
regards it as a differential graded `(A, B)`-bimodule supported in degree zero.  The action of
the DG enveloping algebra is defined explicitly from the ordinary pure-tensor action.  The ground
ring and the algebra/module carriers may live in different universes.
-/

@[expose] public section

noncomputable section

universe u uA uB v

open CategoryTheory Limits ComplexShape HomologicalComplex
open scoped TensorProduct

namespace DifferentialGradedBimodule.DegreeZero

variable {R : Type u} [CommRing R]
variable {A : Type uA} {B : Type uB} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- The underlying `R`-module of an ordinary left-`A`, right-`B` bimodule. -/
abbrev restrictedBimodule (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) : ModuleCat.{max uA uB} R :=
  (ModuleCat.restrictScalars (algebraMap R (A ⊗[R] Bᵐᵒᵖ))).obj N

/-- The single-term cochain complex underlying an ordinary bimodule. -/
noncomputable abbrev complex (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    CochainComplex (ModuleCat.{max uA uB} R) ℤ :=
  (single (ModuleCat.{max uA uB} R) (up ℤ) 0).obj (restrictedBimodule N)

/-- The canonical identification of the degree-zero term with the underlying ordinary
bimodule. -/
noncomputable def zeroIso (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    (complex N).X 0 ≅ restrictedBimodule N :=
  singleObjXSelf (up ℤ) 0 (restrictedBimodule N)

private theorem restricted_smul_assoc
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (r : R)
    (c : A ⊗[R] Bᵐᵒᵖ) (x : restrictedBimodule N) :
    (r • c) • x = r • (c • x) := by
  change (r • c) • (x : N) =
    (algebraMap R (A ⊗[R] Bᵐᵒᵖ) r) • (c • (x : N))
  rw [Algebra.smul_def, mul_smul]

private theorem restricted_smul_comm
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (r : R)
    (c : A ⊗[R] Bᵐᵒᵖ) (x : restrictedBimodule N) :
    c • (r • x) = r • (c • x) := by
  change c • ((algebraMap R (A ⊗[R] Bᵐᵒᵖ) r) • (x : N)) =
    (algebraMap R (A ⊗[R] Bᵐᵒᵖ) r) • (c • (x : N))
  rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- The ordinary action of a pure tensor `a ⊗ bᵒᵖ` on a degree-zero bimodule element. -/
noncomputable def pureActionCurried
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (x : (complex N).X 0) :
    (CochainDGAlgebra.ofAlgebra R A).opposite.X 0 →ₗ[R]
      (CochainDGAlgebra.ofAlgebra R B).X 0 →ₗ[R] (complex N).X 0 where
  toFun a :=
    { toFun := fun b ↦ (zeroIso N).inv
        ((_root_.TensorProduct.tmul R
          ((CochainDGAlgebra.ofAlgebraZeroIso R A).hom a)
          (MulOpposite.op ((CochainDGAlgebra.ofAlgebraZeroIso R B).hom b))) •
            (zeroIso N).hom x)
      map_add' := by
        intro b₁ b₂
        simp [TensorProduct.tmul_add, add_smul]
      map_smul' := by
        intro r b
        simp only [map_smul, RingHom.id_apply, MulOpposite.op_smul,
          TensorProduct.tmul_smul, restricted_smul_assoc]
    }
  map_add' := by
    intro a₁ a₂
    ext b
    simp [TensorProduct.add_tmul, add_smul]
  map_smul' := by
    intro r a
    ext b
    simp only [LinearMap.coe_mk, LinearMap.smul_apply, map_smul, RingHom.id_apply,
      ← TensorProduct.smul_tmul', restricted_smul_assoc]
    rfl

/-- The pure-tensor action as a morphism from the tensor of the two degree-zero components. -/
noncomputable def pureAction
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (x : (complex N).X 0) :
    ModuleCat.Hom (ModuleCat.TensorProduct.obj R
        ((CochainDGAlgebra.ofAlgebra R A).opposite.X 0)
        ((CochainDGAlgebra.ofAlgebra R B).X 0))
      ((complex N).X 0) :=
  ModuleCat.TensorProduct.lift R (pureActionCurried N x)

/-- The summandwise action map defining the action of the degree-zero DG enveloping algebra. -/
noncomputable def actionComponent
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (x : (complex N).X 0) :
    (p q : ℤ) → (up ℤ).π (up ℤ) (up ℤ) (p, q) = 0 →
      ModuleCat.Hom (ModuleCat.TensorProduct.obj R
          ((CochainDGAlgebra.ofAlgebra R A).opposite.X p)
          ((CochainDGAlgebra.ofAlgebra R B).X q))
        ((complex N).X 0) :=
  fun p q ↦ match p, q with
    | 0, 0 => fun (_ : (up ℤ).π (up ℤ) (up ℤ) (0, 0) = 0) ↦
        pureAction N x
    | p, q => fun (_ : (up ℤ).π (up ℤ) (up ℤ) (p, q) = 0) ↦
      ModuleCat.ofHom
          (X := ModuleCat.TensorProduct.obj R
            ((CochainDGAlgebra.ofAlgebra R A).opposite.X p)
            ((CochainDGAlgebra.ofAlgebra R B).X q))
          (Y := (complex N).X 0) 0

/-- The degree-zero action of the DG enveloping algebra on an ordinary bimodule. -/
noncomputable def actionZero
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    (complex N).X 0 →ₗ[R]
      (CochainDGAlgebra.enveloping (CochainDGAlgebra.ofAlgebra R A)
        (CochainDGAlgebra.ofAlgebra R B)).X 0 →ₗ[R]
          (complex N).X 0 where
  toFun x :=
    (mapBifunctorDesc
      (A := (complex N).X 0) (j := 0)
      (K₁ := (CochainDGAlgebra.ofAlgebra R A).opposite.toCochainComplex)
      (K₂ := (CochainDGAlgebra.ofAlgebra R B).toCochainComplex)
      (F := ModuleCat.TensorProduct.functor.{u, uA, uB} R) (c := up ℤ)
      (actionComponent N x)).hom
  map_add' := by
    intro x₁ x₂
    let desc (x : (complex N).X 0) :
        (CochainDGAlgebra.enveloping (CochainDGAlgebra.ofAlgebra R A)
          (CochainDGAlgebra.ofAlgebra R B)).X 0 ⟶ (complex N).X 0 :=
      mapBifunctorDesc
        (K₁ := (CochainDGAlgebra.ofAlgebra R A).opposite.toCochainComplex)
        (K₂ := (CochainDGAlgebra.ofAlgebra R B).toCochainComplex)
        (F := ModuleCat.TensorProduct.functor.{u, uA, uB} R) (c := up ℤ)
        (actionComponent N x)
    have h : desc (x₁ + x₂) = desc x₁ + desc x₂ := by
      apply mapBifunctor.hom_ext
      intro p q h
      simp only [desc, Preadditive.comp_add, ι_mapBifunctorDesc]
      by_cases hp : p = 0
      · subst p
        by_cases hq : q = 0
        · subst q
          ext a b
          change (zeroIso N).inv
              ((TensorProduct.tmul R
                ((CochainDGAlgebra.ofAlgebraZeroIso R A).hom a)
                (MulOpposite.op ((CochainDGAlgebra.ofAlgebraZeroIso R B).hom b))) •
                (zeroIso N).hom (x₁ + x₂)) = _
          simp only [map_add, smul_add]
          rfl
        · simp [actionComponent, hq] <;> rfl
      · simp [actionComponent, hp] <;> rfl
    exact congrArg ModuleCat.Hom.hom h
  map_smul' := by
    intro r x
    let desc (x : (complex N).X 0) :
        (CochainDGAlgebra.enveloping (CochainDGAlgebra.ofAlgebra R A)
          (CochainDGAlgebra.ofAlgebra R B)).X 0 ⟶ (complex N).X 0 :=
      mapBifunctorDesc
        (K₁ := (CochainDGAlgebra.ofAlgebra R A).opposite.toCochainComplex)
        (K₂ := (CochainDGAlgebra.ofAlgebra R B).toCochainComplex)
        (F := ModuleCat.TensorProduct.functor.{u, uA, uB} R) (c := up ℤ)
        (actionComponent N x)
    have h : desc (r • x) = r • desc x := by
      apply mapBifunctor.hom_ext
      intro p q h
      simp only [desc, Linear.comp_smul, ι_mapBifunctorDesc]
      by_cases hp : p = 0
      · subst p
        by_cases hq : q = 0
        · subst q
          ext a b
          change (zeroIso N).inv
              ((TensorProduct.tmul R
                ((CochainDGAlgebra.ofAlgebraZeroIso R A).hom a)
                (MulOpposite.op ((CochainDGAlgebra.ofAlgebraZeroIso R B).hom b))) •
                (zeroIso N).hom (r • x)) = _
          simp only [map_smul, restricted_smul_comm]
          rfl
        · simp [actionComponent, hq]
          apply ModuleCat.hom_ext
          ext z
          exact (smul_zero r).symm
      · simp [actionComponent, hp]
        apply ModuleCat.hom_ext
        ext z
        exact (smul_zero r).symm
    exact congrArg ModuleCat.Hom.hom h

private theorem actionZero_pure
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (x : (complex N).X 0)
    (a : (CochainDGAlgebra.ofAlgebra R A).opposite.X 0)
    (b : (CochainDGAlgebra.ofAlgebra R B).X 0) :
    actionZero N x
        (CochainDGAlgebra.Enveloping.pure
          (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B) a b) =
      (zeroIso N).inv
        ((TensorProduct.tmul R ((CochainDGAlgebra.ofAlgebraZeroIso R A).hom a)
          (MulOpposite.op ((CochainDGAlgebra.ofAlgebraZeroIso R B).hom b))) •
            (zeroIso N).hom x) := by
  exact congrArg
    (fun f : ModuleCat.TensorProduct.obj R
        ((CochainDGAlgebra.ofAlgebra R A).opposite.X 0)
        ((CochainDGAlgebra.ofAlgebra R B).X 0) ⟶ (complex N).X 0 ↦
      f (a ⊗ₜ[R] b))
    (ι_mapBifunctorDesc
      (K₁ := (CochainDGAlgebra.ofAlgebra R A).opposite.toCochainComplex)
      (K₂ := (CochainDGAlgebra.ofAlgebra R B).toCochainComplex)
      (F := ModuleCat.TensorProduct.functor.{u, uA, uB} R) (c := up ℤ)
      (actionComponent N x) 0 0 (CochainDGAlgebra.Tensor.totalDegree 0 0))

/-- The homogeneous DG-enveloping action on an ordinary bimodule supported in degree zero. -/
noncomputable def action
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) : (p i : ℤ) →
    (complex N).X p →ₗ[R]
      (CochainDGAlgebra.enveloping (CochainDGAlgebra.ofAlgebra R A)
        (CochainDGAlgebra.ofAlgebra R B)).X i →ₗ[R]
          (complex N).X (p + i)
  | 0, 0 => actionZero N
  | _, _ => 0

private theorem enveloping_X_subsingleton (n : ℤ) (hn : n ≠ 0) :
    Subsingleton ((CochainDGAlgebra.enveloping (CochainDGAlgebra.ofAlgebra R A)
      (CochainDGAlgebra.ofAlgebra R B)).X n) := by
  apply ModuleCat.subsingleton_of_isZero
  apply (IsZero.iff_id_eq_zero _).mpr
  apply mapBifunctor.hom_ext
  intro p q h
  by_cases hp : p = 0
  · subst p
    have hq : q ≠ 0 := by
      change 0 + q = n at h
      omega
    haveI : Subsingleton ((CochainDGAlgebra.ofAlgebra R B).X q) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_X (up ℤ) 0 (ModuleCat.of R B) q hq)
    exact (ModuleCat.isZero_of_subsingleton
      (ModuleCat.TensorProduct.obj R ((CochainDGAlgebra.ofAlgebra R A).opposite.X 0)
        ((CochainDGAlgebra.ofAlgebra R B).X q))).eq_of_src _ _
  · haveI : Subsingleton ((CochainDGAlgebra.ofAlgebra R A).opposite.X p) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_X (up ℤ) 0 (ModuleCat.of R A) p hp)
    exact (ModuleCat.isZero_of_subsingleton
      (ModuleCat.TensorProduct.obj R ((CochainDGAlgebra.ofAlgebra R A).opposite.X p)
        ((CochainDGAlgebra.ofAlgebra R B).X q))).eq_of_src _ _

private theorem enveloping_d_zero (n : ℤ) :
    (CochainDGAlgebra.enveloping (CochainDGAlgebra.ofAlgebra R A)
      (CochainDGAlgebra.ofAlgebra R B)).toCochainComplex.d n (n + 1) = 0 := by
  by_cases hn : n = 0
  · subst n
    haveI := enveloping_X_subsingleton (R := R) (A := A) (B := B) (0 + 1) (by decide)
    exact (ModuleCat.isZero_of_subsingleton _).eq_of_tgt _ _
  · haveI := enveloping_X_subsingleton (R := R) (A := A) (B := B) n hn
    exact (ModuleCat.isZero_of_subsingleton _).eq_of_src _ _

private theorem cast_zero_of_index_eq (M : ℤ → ModuleCat.{v} R)
    {p q : ℤ} (h : p = q) (e : (M p : Type v) = M q) :
    cast e (0 : M p) = (0 : M q) := by
  subst q
  rfl

/-- An ordinary left-`A`, right-`B` bimodule, regarded as a differential graded bimodule
supported in degree zero. -/
@[stacks 09SC "ordinary bimodule as a degree-zero differential graded bimodule"]
noncomputable def ofBimodule (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    DifferentialGradedBimodule.{u, max uA uB, uA, uB} (CochainDGAlgebra.ofAlgebra R A)
      (CochainDGAlgebra.ofAlgebra R B) where
  X := (complex N).X
  d n := ((complex N).d n (n + 1)).hom
  smul := action N
  d_sq := by simp [complex]
  smul_one := by
    intro r p x
    by_cases hp : p = 0
    · subst p
      change actionZero N x
        (r • (CochainDGAlgebra.enveloping (CochainDGAlgebra.ofAlgebra R A)
          (CochainDGAlgebra.ofAlgebra R B)).one) = r • x
      rw [map_smul]
      congr 1
      change actionZero N x
        (CochainDGAlgebra.Enveloping.pure (CochainDGAlgebra.ofAlgebra R A)
          (CochainDGAlgebra.ofAlgebra R B)
          (CochainDGAlgebra.ofAlgebra R A).one (CochainDGAlgebra.ofAlgebra R B).one) = x
      rw [actionZero_pure]
      have hA : (CochainDGAlgebra.ofAlgebraZeroIso R A).hom
          (CochainDGAlgebra.ofAlgebra R A).one = 1 :=
        congrArg (fun f : ModuleCat.of R A ⟶ ModuleCat.of R A ↦ f 1)
          (CochainDGAlgebra.ofAlgebraZeroIso R A).inv_hom_id
      have hB : (CochainDGAlgebra.ofAlgebraZeroIso R B).hom
          (CochainDGAlgebra.ofAlgebra R B).one = 1 :=
        congrArg (fun f : ModuleCat.of R B ⟶ ModuleCat.of R B ↦ f 1)
          (CochainDGAlgebra.ofAlgebraZeroIso R B).inv_hom_id
      rw [hA, hB, MulOpposite.op_one, ← Algebra.TensorProduct.one_def, one_smul]
      exact congrArg (fun f : (complex N).X 0 ⟶ (complex N).X 0 ↦ f x)
        (zeroIso N).hom_inv_id
    · haveI : Subsingleton ((complex N).X p) := ModuleCat.subsingleton_of_isZero
        (isZero_single_obj_X (up ℤ) 0 (restrictedBimodule N) p hp)
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx, map_zero, LinearMap.zero_apply, smul_zero,
        cast_zero_of_index_eq (complex N).X (by omega)]
  smul_mul := sorry
  comm_d := by
    intro p i x a
    have ha := congrArg (fun f ↦ f.hom a)
      (enveloping_d_zero (R := R) (A := A) (B := B) i)
    simp [complex, ha]
    rw [cast_zero_of_index_eq (complex N).X (by omega),
      cast_zero_of_index_eq (complex N).X (by omega), smul_zero, add_zero]

/-- A morphism of ordinary left-`A`, right-`B` bimodules induces a morphism of their
degree-zero differential graded models. -/
noncomputable def ofBimoduleHom
    {N N' : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)} (f : N ⟶ N') :
    ofBimodule N ⟶ ofBimodule N' where
  hom n := (((single (ModuleCat.{max uA uB} R) (up ℤ) 0).map
    ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] Bᵐᵒᵖ))).map f)).f n).hom
  comm_d := by
    intro n x
    exact ((((single (ModuleCat.{max uA uB} R) (up ℤ) 0).map
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] Bᵐᵒᵖ))).map f)).f (n + 1)).hom.map_zero)
  comm_smul := sorry

private theorem bimoduleHom_ext
    {M M' : DifferentialGradedBimodule.{u, max uA uB, uA, uB}
      (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B)}
    {f g : M ⟶ M'} (h : ∀ n x, f.hom n x = g.hom n x) : f = g := by
  have h' : f.hom = g.hom := funext fun n ↦ LinearMap.ext (h n)
  cases f
  cases g
  cases h'
  rfl

/-- The functor sending an ordinary left-`A`, right-`B` bimodule to its degree-zero
differential graded bimodule. -/
@[stacks 09SC "ordinary bimodules as degree-zero differential graded bimodules"]
noncomputable def ofBimoduleFunctor
    (R : Type u) [CommRing R] (A : Type uA) (B : Type uB) [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] :
    ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ) ⥤
      DifferentialGradedBimodule.{u, max uA uB, uA, uB} (CochainDGAlgebra.ofAlgebra R A)
        (CochainDGAlgebra.ofAlgebra R B) where
  obj := ofBimodule
  map := ofBimoduleHom
  map_id := by
    intro N
    apply bimoduleHom_ext
    intro n x
    dsimp only [ofBimodule] at x
    change (((single (ModuleCat.{max uA uB} R) (up ℤ) 0).map
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] Bᵐᵒᵖ))).map (𝟙 N))).f n).hom x = x
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  map_comp := by
    intro N N' N'' f g
    apply bimoduleHom_ext
    intro n x
    dsimp only [ofBimodule] at x
    change (((single (ModuleCat.{max uA uB} R) (up ℤ) 0).map
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] Bᵐᵒᵖ))).map (f ≫ g))).f n).hom x =
        (((single (ModuleCat.{max uA uB} R) (up ℤ) 0).map
          ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] Bᵐᵒᵖ))).map g)).f n).hom
            ((((single (ModuleCat.{max uA uB} R) (up ℤ) 0).map
              ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] Bᵐᵒᵖ))).map f)).f n).hom x)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- The underlying graded object of `ofBimodule` is the single-term complex of the ordinary
bimodule. -/
@[simp]
theorem ofBimodule_X (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (n : ℤ) :
    (ofBimodule N).X n = (complex N).X n := rfl

/-- The degreewise map of `ofBimoduleHom` is the single-complex map induced after restriction
of scalars to `R`. -/
@[simp]
theorem ofBimoduleHom_hom
    {N N' : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)} (f : N ⟶ N') (n : ℤ) :
    (ofBimoduleHom f).hom n =
      (((single (ModuleCat.{max uA uB} R) (up ℤ) 0).map
        ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] Bᵐᵒᵖ))).map f)).f n).hom := rfl

/-- The degree-zero bimodule functor has `ofBimodule` as its object map. -/
@[simp]
theorem ofBimoduleFunctor_obj (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    (ofBimoduleFunctor R A B).obj N = ofBimodule N := rfl

/-- The degree-zero bimodule functor has `ofBimoduleHom` as its morphism map. -/
@[simp]
theorem ofBimoduleFunctor_map
    {N N' : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)} (f : N ⟶ N') :
    (ofBimoduleFunctor R A B).map f = ofBimoduleHom f := rfl

/-- Degree zero of `ofBimodule` is canonically the underlying ordinary bimodule. -/
@[stacks 09SC "degree-zero identification of an ordinary bimodule"]
noncomputable def ofBimoduleZeroIso (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) :
    (ofBimodule N).X 0 ≅ restrictedBimodule N :=
  zeroIso N

/-- On a pure degree-zero enveloping tensor, `ofBimodule` acts by
`(a ⊗ bᵒᵖ) • x`. -/
@[simp]
theorem ofBimodule_smul_pure
    (N : ModuleCat.{max uA uB} (A ⊗[R] Bᵐᵒᵖ)) (x : (ofBimodule N).X 0)
    (a : (CochainDGAlgebra.ofAlgebra R A).opposite.X 0)
    (b : (CochainDGAlgebra.ofAlgebra R B).X 0) :
    (ofBimodule N).smul 0 0 x
        (CochainDGAlgebra.Enveloping.pure
          (CochainDGAlgebra.ofAlgebra R A) (CochainDGAlgebra.ofAlgebra R B) a b) =
      (ofBimoduleZeroIso N).inv
        ((_root_.TensorProduct.tmul R
          ((CochainDGAlgebra.ofAlgebraZeroIso R A).hom a)
          (MulOpposite.op ((CochainDGAlgebra.ofAlgebraZeroIso R B).hom b))) •
            (ofBimoduleZeroIso N).hom x) := by
  exact congrArg
    (fun f : ModuleCat.TensorProduct.obj R
        ((CochainDGAlgebra.ofAlgebra R A).opposite.X 0)
        ((CochainDGAlgebra.ofAlgebra R B).X 0) ⟶ (complex N).X 0 ↦
      f (a ⊗ₜ[R] b))
    (ι_mapBifunctorDesc
      (K₁ := (CochainDGAlgebra.ofAlgebra R A).opposite.toCochainComplex)
      (K₂ := (CochainDGAlgebra.ofAlgebra R B).toCochainComplex)
      (F := ModuleCat.TensorProduct.functor.{u, uA, uB} R) (c := up ℤ)
      (actionComponent N x) 0 0 (CochainDGAlgebra.Tensor.totalDegree 0 0))

end DifferentialGradedBimodule.DegreeZero
