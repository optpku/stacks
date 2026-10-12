/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
  left_inv := sorry
  right_inv := sorry

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
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

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
    f n = toLinearMap N P f n := sorry

/-- The observation map agrees with the underlying total homogeneous-map sum. -/
@[simp]
theorem toLinearMap_apply (f : InternalHom N P) (n : N) :
    toLinearMap N P f n = Right.Hom.toLinearMap N.toRight P f.toHom n := sorry

/-- Graded internal-Hom elements are determined by their underlying homogeneous-map sum. -/
@[ext]
theorem ext {f g : InternalHom N P} (h : f.toHom = g.toHom) : f = g := sorry

/-- Unwrapping a wrapped homogeneous-map sum returns the original sum. -/
@[simp]
theorem toHom_ofHom (f : Right.Hom N.toRight P) : (ofHom f).toHom = f := sorry

/-- Rewrapping the underlying homogeneous-map sum returns the original element. -/
@[simp]
theorem ofHom_toHom (f : InternalHom N P) : ofHom f.toHom = f := sorry

/-- Include a single homogeneous right-linear map into the graded internal Hom. -/
def ofHomogeneous (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (k : ι) :
    Right.HomogeneousMap N.toRight P k →ₗ[R] InternalHom N P :=
  (linearEquiv (N := N) (P := P)).symm.toLinearMap.comp
    (Right.Hom.of N.toRight P k)

/-- Unwrapping the inclusion of one homogeneous map gives its canonical direct-sum inclusion. -/
@[simp]
theorem toHom_ofHomogeneous (k : ι) (f : Right.HomogeneousMap N.toRight P k) :
    (ofHomogeneous N P k f).toHom = Right.Hom.of N.toRight P k f := sorry

/-- Forgetting the decomposition after including one homogeneous map returns that map. -/
@[simp]
theorem toLinearMap_ofHomogeneous (k : ι)
    (f : Right.HomogeneousMap N.toRight P k) :
    toLinearMap N P (ofHomogeneous N P k f) = f.1 := sorry

/-- Evaluation after including one homogeneous map is ordinary evaluation. -/
@[simp]
theorem ofHomogeneous_apply (k : ι) (f : Right.HomogeneousMap N.toRight P k) (n : N) :
    ofHomogeneous N P k f n = f.1 n := sorry

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
    (homogeneousMapEquivGrading N P k f).1 = ofHomogeneous N P k f := sorry

/-- Extracting and reincluding a member of one internal-Hom degree changes nothing. -/
@[simp]
theorem homogeneousMapEquivGrading_symm_apply (k : ι) (f : grading N P k) :
    ofHomogeneous N P k ((homogeneousMapEquivGrading N P k).symm f) = f.1 := sorry

/-- A homogeneous map included into the internal Hom lies in its matching degree. -/
@[simp]
theorem ofHomogeneous_mem (k : ι) (f : Right.HomogeneousMap N.toRight P k) :
    ofHomogeneous N P k f ∈ grading N P k := sorry

/-- Membership in the degree-`k` piece is membership of the underlying sum in the corresponding
homogeneous-map summand. -/
@[simp]
theorem mem_grading_iff (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (k : ι) (f : InternalHom N P) :
    f ∈ grading N P k ↔ f.toHom ∈ Right.homDegree N.toRight P k := sorry

/-- Precomposition by a homogeneous element of `A` adds its degree to a homogeneous right-linear
map. -/
theorem smul_mem (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) {k j : ι}
    {f : Module.Bimodule.InternalHom B N P} {a : A}
    (hf : f.toLinearMap ∈ Right.HomogeneousMap N.toRight P k) (ha : a ∈ 𝒜 j) :
    (MulOpposite.op a • f).toLinearMap ∈
      Right.HomogeneousMap N.toRight P (k + j) := sorry

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
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- Extend precomposition by one homogeneous algebra component across all map degrees. -/
def degreeAction (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (j : ι) :
    𝒜 j →ₗ[R] Right.Hom N.toRight P →ₗ[R] Right.Hom N.toRight P where
  toFun a := DirectSum.toModule R ι _ (fun k ↦ componentAction N P j k a)
  map_add' := sorry
  map_smul' := sorry

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

/-- The canonical right `A`-action on graded internal Hom is precomposition. -/
instance instModuleOpposite : Module Aᵐᵒᵖ (InternalHom N P) where
  smul a f := ofHom (action N P a f.toHom)
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The base-ring action and the precomposition action form a scalar tower. -/
instance instIsScalarTower : IsScalarTower R Aᵐᵒᵖ (InternalHom N P) :=
  ⟨sorry⟩

/-- The precomposition action respects the transported internal-Hom grading. -/
instance instGradedSMul :
    SetLike.GradedSMul (oppositeGrading 𝒜) (grading N P) :=
  ⟨sorry⟩

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
  map_add' := sorry
  map_smul' := sorry

/-- Collapsing an internal-Hom element does not change its evaluation. -/
@[simp]
theorem collapse_apply (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (f : InternalHom N P) (n : N) :
    collapse N P f n = f n := sorry

/-- The carrier of `obj N P` is the instance-safe graded internal-Hom wrapper. -/
@[simp]
theorem obj_carrier (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) : (obj N P).carrier = InternalHom N P := sorry

/-- The grading of `obj N P` is the transported homogeneous-map grading. -/
@[simp]
theorem obj_grading (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (k : ι) :
    (obj N P).grading k = grading N P k := sorry

/-- Collapsing an element included from one homogeneous degree returns its underlying map. -/
@[simp]
theorem collapse_of (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) (k : ι)
    (f : Right.HomogeneousMap N.toRight P k) :
    collapse N P (ofHomogeneous N P k f) =
      Module.Bimodule.InternalHom.ofLinearMap (B := B) f.1 := sorry

end InternalHom

end GradedModule
