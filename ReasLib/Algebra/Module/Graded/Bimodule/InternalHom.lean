/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.DirectSum.Decomposition.Transport
public import ReasLib.Algebra.Module.Bimodule.InternalHom
public import ReasLib.Algebra.Module.Graded.Bimodule

/-!
# Graded Internal Hom for Bimodules

The graded internal Hom is a dedicated wrapper around the direct sum of homogeneous right-linear
maps.  The wrapper remembers the bimodule supplying the left action, so its canonical
precomposition instance cannot conflict with another left action on the same raw map space.
-/

@[expose] public section

noncomputable section

namespace GradedModule

open scoped DirectSum

universe i u v w x y z

variable {ι : Type i} [DecidableEq ι] [AddCommMonoid ι]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
variable {𝒝 : ι → Submodule R B} [GradedAlgebra 𝒝]

/-- The direct sum of homogeneous right-`B`-linear maps, wrapped with the bimodule that supplies
the canonical right `A`-action by precomposition. -/
@[stacks 09LN "graded relative internal Hom carrier"]
structure InternalHom (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) where
  /-- The underlying finite sum of homogeneous right-`B`-linear maps. -/
  toHom : Right.Hom N.toRight P

namespace InternalHom

variable {N : Bimodule.{i, y, w, v, u} 𝒜 𝒝}
variable {P : Right.{i, z, w, u} 𝒝}

/-- Wrap a finite sum of homogeneous maps as a graded internal-Hom element. -/
def ofHom (f : Right.Hom N.toRight P) : InternalHom N P :=
  ⟨f⟩

/-- The wrapped graded internal Hom is equivalent to its underlying homogeneous-map direct sum. -/
def equiv : InternalHom N P ≃ Right.Hom N.toRight P where
  toFun := InternalHom.toHom
  invFun := ofHom
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- The additive group structure transported from the homogeneous-map direct sum. -/
instance instAddCommGroup : AddCommGroup (InternalHom N P) :=
  (equiv (N := N) (P := P)).addCommGroup

/-- The base-ring module structure transported from the homogeneous-map direct sum. -/
instance instModuleBase : Module R (InternalHom N P) :=
  (equiv (N := N) (P := P)).module R

/-- The wrapped graded internal Hom is linearly equivalent to its homogeneous-map direct sum. -/
def linearEquiv : InternalHom N P ≃ₗ[R] Right.Hom N.toRight P where
  toFun := InternalHom.toHom
  invFun := ofHom
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

/-- Forget the finite homogeneous decomposition and observe a graded internal-Hom element as its
underlying right-linear map. -/
def toLinearMap (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) :
    InternalHom N P →ₗ[R] (N →ₗ[Bᵐᵒᵖ] P) :=
  (Right.Hom.toLinearMap N.toRight P).comp
    (linearEquiv (N := N) (P := P)).toLinearMap

/-- A graded internal-Hom element acts on the source through its underlying right-linear map. -/
instance instCoeFun : CoeFun (InternalHom N P) (fun _ ↦ N → P) where
  coe f := toLinearMap N P f

/-- Evaluation of a graded internal-Hom element is evaluation of its underlying right-linear map. -/
@[simp]
theorem coe_apply (f : InternalHom N P) (n : N) :
    f n = toLinearMap N P f n := rfl

/-- The observation map agrees with the underlying total homogeneous-map sum. -/
@[simp]
theorem toLinearMap_apply (f : InternalHom N P) (n : N) :
    toLinearMap N P f n = Right.Hom.toLinearMap N.toRight P f.toHom n := rfl

/-- Graded internal-Hom elements are determined by their underlying homogeneous-map sum. -/
@[ext]
theorem ext {f g : InternalHom N P} (h : f.toHom = g.toHom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Unwrapping a wrapped homogeneous-map sum returns the original sum. -/
@[simp]
theorem toHom_ofHom (f : Right.Hom N.toRight P) : (ofHom f).toHom = f := rfl

/-- Rewrapping the underlying homogeneous-map sum returns the original element. -/
@[simp]
theorem ofHom_toHom (f : InternalHom N P) : ofHom f.toHom = f := rfl

/-- Include a single homogeneous right-linear map into the graded internal Hom. -/
def ofHomogeneous (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (k : ι) :
    Right.HomogeneousMap N.toRight P k →ₗ[R] InternalHom N P :=
  (linearEquiv (N := N) (P := P)).symm.toLinearMap.comp
    (Right.Hom.of N.toRight P k)

/-- Unwrapping the inclusion of one homogeneous map gives its canonical direct-sum inclusion. -/
@[simp]
theorem toHom_ofHomogeneous (k : ι) (f : Right.HomogeneousMap N.toRight P k) :
    (ofHomogeneous N P k f).toHom = Right.Hom.of N.toRight P k f := rfl

/-- Forgetting the decomposition after including one homogeneous map returns that map. -/
@[simp]
theorem toLinearMap_ofHomogeneous (k : ι)
    (f : Right.HomogeneousMap N.toRight P k) :
    toLinearMap N P (ofHomogeneous N P k f) = f.1 := by
  change Right.Hom.toLinearMap N.toRight P (Right.Hom.of N.toRight P k f) = f.1
  exact DirectSum.toModule_lof R (φ := fun k ↦ (Right.HomogeneousMap N.toRight P k).subtype) k f

/-- Evaluation after including one homogeneous map is ordinary evaluation. -/
@[simp]
theorem ofHomogeneous_apply (k : ι) (f : Right.HomogeneousMap N.toRight P k) (n : N) :
    ofHomogeneous N P k f n = f.1 n := by
  exact congrArg (fun g : N →ₗ[Bᵐᵒᵖ] P ↦ g n) (toLinearMap_ofHomogeneous k f)

/-- The degree-`k` submodule of the wrapped graded internal Hom. -/
def grading (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) (P : Right.{i, z, w, u} 𝒝) (k : ι) :
    Submodule R (InternalHom N P) :=
  (Right.homDegree N.toRight P k).map (linearEquiv (N := N) (P := P)).symm.toLinearMap

/-- The wrapped internal-Hom grading is the transport of the canonical grading on homogeneous-map
sums. -/
instance instDecomposition (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) : DirectSum.Decomposition (grading N P) :=
  DirectSum.Decomposition.map (Right.homDegree N.toRight P)
    (linearEquiv (N := N) (P := P)).symm

/-- Homogeneous right-linear maps are canonically the corresponding graded internal-Hom
piece. -/
def homogeneousMapEquivGrading (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (k : ι) :
    Right.HomogeneousMap N.toRight P k ≃ₗ[R] grading N P k :=
  (Right.homogeneousMapEquivDegree N.toRight P k).trans
    ((linearEquiv (N := N) (P := P)).symm.submoduleMap
      (Right.homDegree N.toRight P k))

/-- The homogeneous-map equivalence has `ofHomogeneous` as its underlying inclusion. -/
@[simp]
theorem homogeneousMapEquivGrading_apply (k : ι)
    (f : Right.HomogeneousMap N.toRight P k) :
    (homogeneousMapEquivGrading N P k f).1 = ofHomogeneous N P k f := rfl

/-- Extracting and reincluding a member of one internal-Hom degree changes nothing. -/
@[simp]
theorem homogeneousMapEquivGrading_symm_apply (k : ι) (f : grading N P k) :
    ofHomogeneous N P k ((homogeneousMapEquivGrading N P k).symm f) = f.1 := by
  exact congrArg Subtype.val ((homogeneousMapEquivGrading N P k).apply_symm_apply f)

/-- A homogeneous map included into the internal Hom lies in its matching degree. -/
@[simp]
theorem ofHomogeneous_mem (k : ι) (f : Right.HomogeneousMap N.toRight P k) :
    ofHomogeneous N P k f ∈ grading N P k := by
  exact (homogeneousMapEquivGrading N P k f).2

/-- Membership in the degree-`k` piece is membership of the underlying sum in the corresponding
homogeneous-map summand. -/
@[simp]
theorem mem_grading_iff (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (k : ι) (f : InternalHom N P) :
    f ∈ grading N P k ↔ f.toHom ∈ Right.homDegree N.toRight P k := by
  constructor
  · rintro ⟨g, hg, hgf⟩
    have h : g = f.toHom := congrArg InternalHom.toHom hgf
    exact h ▸ hg
  · intro hf
    exact ⟨f.toHom, hf, rfl⟩

/-- Precomposition by a homogeneous element of `A` adds its degree to a homogeneous right-linear
map. -/
theorem smul_mem (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) {k j : ι}
    {f : Module.Bimodule.InternalHom B N P} {a : A}
    (hf : f.toLinearMap ∈ Right.HomogeneousMap N.toRight P k) (ha : a ∈ 𝒜 j) :
    (MulOpposite.op a • f).toLinearMap ∈
      Right.HomogeneousMap N.toRight P (k + j) := by
  intro i n hn
  have hmem : a • n ∈ N.grading (j + i) := SetLike.GradedSMul.smul_mem ha hn
  change f.toLinearMap (a • n) ∈ P.grading (i + (k + j))
  simpa only [add_assoc, add_comm, add_left_comm] using hf (j + i) (a • n) hmem

/-- Precompose one homogeneous map by one homogeneous element of the left algebra. -/
def smulHomogeneous (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) {j k : ι} (a : 𝒜 j)
    (f : Right.HomogeneousMap N.toRight P k) :
    Right.HomogeneousMap N.toRight P (k + j) :=
  ⟨(MulOpposite.op a.1 •
      Module.Bimodule.InternalHom.ofLinearMap (B := B) f.1).toLinearMap,
    smul_mem N P f.2 a.2⟩

/-- Precomposition by a homogeneous algebra component, included in the total graded Hom. -/
def componentAction (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (j k : ι) :
    𝒜 j →ₗ[R] Right.HomogeneousMap N.toRight P k →ₗ[R] Right.Hom N.toRight P where
  toFun a :=
    { toFun := fun f ↦ Right.Hom.of N.toRight P (k + j) (smulHomogeneous N P a f)
      map_add' := by
        intro f g
        exact (Right.Hom.of N.toRight P (k + j)).map_add
          (smulHomogeneous N P a f) (smulHomogeneous N P a g)
      map_smul' := by
        intro r f
        exact (Right.Hom.of N.toRight P (k + j)).map_smul r
          (smulHomogeneous N P a f) }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro f
    change Right.Hom.of N.toRight P (k + j) (smulHomogeneous N P (a + b) f) =
      Right.Hom.of N.toRight P (k + j) (smulHomogeneous N P a f) +
        Right.Hom.of N.toRight P (k + j) (smulHomogeneous N P b f)
    have h : smulHomogeneous N P (a + b) f =
        smulHomogeneous N P a f + smulHomogeneous N P b f := by
      apply Subtype.ext
      apply LinearMap.ext
      intro n
      change f.1 ((a.1 + b.1) • n) = f.1 (a.1 • n) + f.1 (b.1 • n)
      rw [add_smul, map_add]
    exact (congrArg (Right.Hom.of N.toRight P (k + j)) h).trans
      ((Right.Hom.of N.toRight P (k + j)).map_add _ _)
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro f
    change Right.Hom.of N.toRight P (k + j) (smulHomogeneous N P (r • a) f) =
      r • Right.Hom.of N.toRight P (k + j) (smulHomogeneous N P a f)
    have h : smulHomogeneous N P (r • a) f = r • smulHomogeneous N P a f := by
      apply Subtype.ext
      apply LinearMap.ext
      intro n
      change f.1 ((r • a.1) • n) = r • f.1 (a.1 • n)
      exact (congrArg f.1 (smul_assoc r a.1 n)).trans
        (f.1.map_smul_of_tower r (a.1 • n))
    exact (congrArg (Right.Hom.of N.toRight P (k + j)) h).trans
      ((Right.Hom.of N.toRight P (k + j)).map_smul r _)

/-- Extend precomposition by one homogeneous algebra component across all map degrees. -/
def degreeAction (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (j : ι) :
    𝒜 j →ₗ[R] Right.Hom N.toRight P →ₗ[R] Right.Hom N.toRight P where
  toFun a := DirectSum.toModule R ι _ (fun k ↦ componentAction N P j k a)
  map_add' := by
    intro a b
    apply DirectSum.linearMap_ext
    intro k
    apply LinearMap.ext
    intro f
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof, map_add,
      LinearMap.add_apply]
  map_smul' := by
    intro r a
    apply DirectSum.linearMap_ext
    intro k
    apply LinearMap.ext
    intro f
    simp only [LinearMap.comp_apply, DirectSum.toModule_lof, map_smul,
      LinearMap.smul_apply, RingHom.id_apply]

/-- Extend precomposition linearly across the homogeneous decomposition of the left algebra. -/
def decomposedAction (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) :
    DirectSum ι (fun j ↦ 𝒜 j) →ₗ[R]
      Right.Hom N.toRight P →ₗ[R] Right.Hom N.toRight P :=
  DirectSum.toModule R ι _ (degreeAction N P)

/-- Decompose an element of `Aᵐᵒᵖ` into the homogeneous pieces of `A`. -/
def oppositeDecompose : Aᵐᵒᵖ →ₗ[R] DirectSum ι (fun j ↦ 𝒜 j) :=
  (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap.comp
    (MulOpposite.opLinearEquiv R).symm.toLinearMap

/-- The explicit precomposition action on the underlying homogeneous-map direct sum. -/
def action (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) :
    Aᵐᵒᵖ →ₗ[R] Right.Hom N.toRight P →ₗ[R] Right.Hom N.toRight P :=
  (decomposedAction N P).comp oppositeDecompose

private theorem action_op_coe (j : ι) (a : 𝒜 j) :
    action N P (MulOpposite.op a.1) = degreeAction N P j a := by
  change decomposedAction N P (DirectSum.decomposeLinearEquiv 𝒜 a.1) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe]
  exact DirectSum.toModule_lof R (φ := degreeAction N P) j a

private theorem action_op_coe_of (j k : ι) (a : 𝒜 j)
    (f : Right.HomogeneousMap N.toRight P k) :
    action N P (MulOpposite.op a.1) (Right.Hom.of N.toRight P k f) =
      Right.Hom.of N.toRight P (k + j) (smulHomogeneous N P a f) := by
  rw [action_op_coe j a]
  exact DirectSum.toModule_lof R (φ := fun k ↦ componentAction N P j k a) k f

private theorem hom_of_eq {k l : ι} (h : k = l)
    (f : Right.HomogeneousMap N.toRight P k) (g : Right.HomogeneousMap N.toRight P l)
    (hfg : f.1 = g.1) : Right.Hom.of N.toRight P k f = Right.Hom.of N.toRight P l g := by
  subst l
  exact congrArg (Right.Hom.of N.toRight P k) (Subtype.ext hfg)

private theorem action_one : action N P 1 = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro k
  apply LinearMap.ext
  intro f
  change action N P (MulOpposite.op (1 : A)) (Right.Hom.of N.toRight P k f) =
    Right.Hom.of N.toRight P k f
  rw [action_op_coe_of (N := N) (P := P) 0 k ⟨1, SetLike.one_mem_graded 𝒜⟩]
  apply hom_of_eq (add_zero k)
  apply LinearMap.ext
  intro n
  change f.1 ((1 : A) • n) = f.1 n
  rw [one_smul]

private theorem action_mul_op (a b : A) :
    action N P (MulOpposite.op (a * b)) =
      (action N P (MulOpposite.op b)).comp (action N P (MulOpposite.op a)) := by
  induction a using DirectSum.Decomposition.inductionOn (ℳ := 𝒜) with
  | zero => simp only [zero_mul, MulOpposite.op_zero, map_zero, LinearMap.comp_zero]
  | @homogeneous j a =>
    induction b using DirectSum.Decomposition.inductionOn (ℳ := 𝒜) with
    | zero => simp only [mul_zero, MulOpposite.op_zero, map_zero, LinearMap.zero_comp]
    | @homogeneous l b =>
      apply DirectSum.linearMap_ext
      intro k
      apply LinearMap.ext
      intro f
      change action N P (MulOpposite.op (a.1 * b.1)) (Right.Hom.of N.toRight P k f) =
        action N P (MulOpposite.op b.1)
          (action N P (MulOpposite.op a.1) (Right.Hom.of N.toRight P k f))
      rw [action_op_coe_of (N := N) (P := P) (j + l) k
        ⟨a.1 * b.1, SetLike.mul_mem_graded a.2 b.2⟩,
        action_op_coe_of j k a, action_op_coe_of l (k + j) b]
      apply hom_of_eq (add_assoc k j l).symm
      apply LinearMap.ext
      intro n
      change f.1 ((a.1 * b.1) • n) = f.1 (a.1 • (b.1 • n))
      rw [mul_smul]
    | add b c hb hc =>
      simp only [mul_add, MulOpposite.op_add, map_add, hb, hc, LinearMap.add_comp]
  | add a c ha hc =>
    simp only [add_mul, MulOpposite.op_add, map_add, ha, hc, LinearMap.comp_add]

private theorem toLinearMap_action_op (a : A) (f : Right.Hom N.toRight P) (n : N) :
    Right.Hom.toLinearMap N.toRight P (action N P (MulOpposite.op a) f) n =
      Right.Hom.toLinearMap N.toRight P f (a • n) := by
  induction a using DirectSum.Decomposition.inductionOn (ℳ := 𝒜) with
  | zero =>
    simp only [MulOpposite.op_zero, map_zero, LinearMap.zero_apply, zero_smul]
  | @homogeneous j a =>
    induction f using DirectSum.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | of k f =>
      change Right.Hom.toLinearMap N.toRight P
          (action N P (MulOpposite.op a.1) (Right.Hom.of N.toRight P k f)) n =
        Right.Hom.toLinearMap N.toRight P (Right.Hom.of N.toRight P k f) (a.1 • n)
      rw [action_op_coe_of j k a]
      simp only [Right.Hom.toLinearMap, DirectSum.toModule_lof]
      rfl
    | add f g hf hg =>
      simp only [map_add, LinearMap.add_apply, hf, hg]
  | add a b ha hb =>
    simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, add_smul, ha, hb]

/-- The canonical right `A`-action on graded internal Hom is precomposition. -/
instance instModuleOpposite : Module Aᵐᵒᵖ (InternalHom N P) where
  smul a f := ofHom (action N P a f.toHom)
  one_smul := by
    intro f
    apply ext
    exact congrArg (fun g ↦ g f.toHom) (action_one (N := N) (P := P))
  mul_smul := by
    intro a b f
    apply ext
    exact congrArg (fun g ↦ g f.toHom)
      (action_mul_op (N := N) (P := P) (MulOpposite.unop b) (MulOpposite.unop a))
  smul_zero := by
    intro a
    apply ext
    exact map_zero (action N P a)
  smul_add := by
    intro a f g
    apply ext
    exact map_add (action N P a) f.toHom g.toHom
  add_smul := by
    intro a b f
    apply ext
    exact congrArg (fun g ↦ g f.toHom) (map_add (action N P) a b)
  zero_smul := by
    intro f
    apply ext
    exact congrArg (fun g ↦ g f.toHom) (map_zero (action N P))

/-- The base-ring action and the precomposition action form a scalar tower. -/
instance instIsScalarTower : IsScalarTower R Aᵐᵒᵖ (InternalHom N P) :=
  ⟨fun r a f ↦ by
    apply ext
    exact congrArg (fun g ↦ g f.toHom) (map_smul (action N P) r a)⟩

/-- The precomposition action respects the transported internal-Hom grading. -/
instance instGradedSMul :
    SetLike.GradedSMul (oppositeGrading 𝒜) (grading N P) :=
  ⟨by
    intro j k a f ha hf
    rcases ha with ⟨a, ha, rfl⟩
    rcases (mem_grading_iff N P k f).mp hf with ⟨g, hg⟩
    have h : MulOpposite.op a • f =
        ofHomogeneous N P (k + j) (smulHomogeneous N P ⟨a, ha⟩ g) := by
      apply ext
      change action N P (MulOpposite.op a) f.toHom = _
      rw [← hg]
      exact action_op_coe_of j k ⟨a, ha⟩ g
    change MulOpposite.op a • f ∈ grading N P (j + k)
    rw [h]
    simpa only [add_comm j k] using
      ofHomogeneous_mem (N := N) (P := P) (k + j) (smulHomogeneous N P ⟨a, ha⟩ g)⟩

/-- The graded internal Hom as a right graded `A`-module. -/
@[stacks 09LN "graded relative internal Hom object"]
def obj (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) (P : Right.{i, z, w, u} 𝒝) :
    Right.{i, max i y z, v, u} 𝒜 where
  carrier := InternalHom N P
  addCommGroup := inferInstance
  moduleBase := inferInstance
  moduleOpposite := inferInstance
  isScalarTower := inferInstance
  grading := grading N P
  decomposition := instDecomposition N P
  gradedSMul := inferInstance

/-- Forget the finite homogeneous decomposition and obtain the ordinary wrapped internal-Hom
map. -/
def collapse (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) :
    InternalHom N P →ₗ[Aᵐᵒᵖ] Module.Bimodule.InternalHom B N P where
  toFun f := Module.Bimodule.InternalHom.ofLinearMap (B := B)
    (toLinearMap N P f)
  map_add' := by
    intro f g
    apply ULift.ext
    exact map_add (toLinearMap N P) f g
  map_smul' := by
    intro a f
    apply ULift.ext
    apply LinearMap.ext
    intro n
    exact toLinearMap_action_op (MulOpposite.unop a) f.toHom n

/-- Collapsing an internal-Hom element does not change its evaluation. -/
@[simp]
theorem collapse_apply (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (f : InternalHom N P) (n : N) :
    collapse N P f n = f n := rfl

/-- The carrier of `obj N P` is the instance-safe graded internal-Hom wrapper. -/
@[simp]
theorem obj_carrier (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) : (obj N P).carrier = InternalHom N P := rfl

/-- The grading of `obj N P` is the transported homogeneous-map grading. -/
@[simp]
theorem obj_grading (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (k : ι) :
    (obj N P).grading k = grading N P k := rfl

/-- Collapsing an element included from one homogeneous degree returns its underlying map. -/
@[simp]
theorem collapse_of (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (k : ι)
    (f : Right.HomogeneousMap N.toRight P k) :
    collapse N P (ofHomogeneous N P k f) =
      Module.Bimodule.InternalHom.ofLinearMap (B := B) f.1 := by
  exact congrArg (Module.Bimodule.InternalHom.ofLinearMap (B := B))
    (toLinearMap_ofHomogeneous k f)

end InternalHom

end GradedModule
