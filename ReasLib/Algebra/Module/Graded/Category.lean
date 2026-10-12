/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Module.Equiv.Opposite
public import Mathlib.Algebra.Module.GradedModule
public import ReasLib.CategoryTheory.Graded.DegreeZero
public import ReasLib.Algebra.Module.Graded.HomogeneousMap.Translation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The graded category of right graded modules

This file packages the standard mathlib presentation of an internally graded algebra, namely a
family `𝒜 : ι → Submodule R A` with a `GradedAlgebra 𝒜` instance.  A right graded module uses the
opposite algebra action, a `DirectSum.Decomposition` of its homogeneous pieces, and
`SetLike.GradedSMul` for compatibility of the action with those pieces.

Morphisms in the ambient graded category are finite sums of homogeneous right-linear maps.  The
ordinary category of graded modules is its degree-zero category.

The short `Right.HomogeneousMap` operations below are reducible typed bridges to the generic
translation owner; this module owns the right-module model and total graded category, not a second
homogeneous-map data representation.
-/

@[expose] public section

noncomputable section

universe x w v u

open CategoryTheory

namespace GradedModule

variable {ι : Type x}
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]

/-- The grading on `Aᵐᵒᵖ` obtained from an internal grading on `A`. -/
def oppositeGrading (𝒜 : ι → Submodule R A) : ι → Submodule R Aᵐᵒᵖ :=
  fun i ↦ (𝒜 i).map (MulOpposite.opLinearEquiv R).toLinearMap

/-- Membership in `oppositeGrading 𝒜` is membership in the corresponding piece of `𝒜`. -/
@[simp]
theorem op_mem_oppositeGrading_iff (𝒜 : ι → Submodule R A) {i : ι} {a : A} :
    MulOpposite.op a ∈ oppositeGrading 𝒜 i ↔ a ∈ 𝒜 i := sorry

variable [DecidableEq ι] [AddCommMonoid ι]

/-- A right graded module over the internally graded algebra `𝒜`.

The mathematical payload is the right `A`-module, its internal direct-sum grading, and the
canonical mathlib `SetLike.GradedSMul` compatibility condition. -/
@[stacks 09MN "right graded modules over an internally graded algebra"]
structure Right (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] where
  /-- The underlying type. -/
  carrier : Type w
  /-- The additive group of the underlying module. -/
  [addCommGroup : AddCommGroup carrier]
  /-- The underlying `R`-module. -/
  [moduleBase : Module R carrier]
  /-- The right `A`-module, represented as a left `Aᵐᵒᵖ`-module. -/
  [moduleOpposite : Module Aᵐᵒᵖ carrier]
  /-- Restriction of the right action along `R → Aᵐᵒᵖ` agrees with the `R`-module structure. -/
  [isScalarTower : IsScalarTower R Aᵐᵒᵖ carrier]
  /-- The homogeneous pieces of the module. -/
  grading : ι → Submodule R carrier
  /-- The homogeneous pieces form an internal direct-sum decomposition. -/
  [decomposition : DirectSum.Decomposition grading]
  /-- The right action adds the degree of a homogeneous algebra element. -/
  [gradedSMul : SetLike.GradedSMul (oppositeGrading 𝒜) grading]

namespace Right

variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

attribute [instance] Right.addCommGroup Right.moduleBase Right.moduleOpposite
  Right.isScalarTower Right.decomposition Right.gradedSMul

/-- A right graded module coerces to its underlying type. -/
instance instCoeSort : CoeSort (Right (R := R) (A := A) 𝒜) (Type w) where
  coe M := M.carrier

/-- The stored right action of a graded module. -/
def action (M : Right (R := R) (A := A) 𝒜) (x : M) (a : A) : M :=
  MulOpposite.op a • x

/-- Right multiplication by homogeneous elements adds their degrees. -/
theorem smul_mem (M : Right (R := R) (A := A) 𝒜) {i j : ι} {x : M} {a : A}
    (hx : x ∈ M.grading i) (ha : a ∈ 𝒜 j) :
    M.action x a ∈ M.grading (i + j) := sorry

/-- A homogeneous right-linear map of degree `n` between right graded modules. -/
@[stacks 09MN "homogeneous maps between right graded modules"]
abbrev HomogeneousMap (L M : Right (R := R) (A := A) 𝒜) (n : ι) :=
  GradedModule.HomogeneousMap Aᵐᵒᵖ L.grading M.grading n

/-- A right-linear map is homogeneous of degree `n` exactly when it sends the degree-`i`
piece into the degree-`i + n` piece for every `i`. -/
@[simp]
theorem HomogeneousMap.mem_iff (L M : Right (R := R) (A := A) 𝒜) (n : ι)
    (f : L →ₗ[Aᵐᵒᵖ] M) :
    f ∈ HomogeneousMap L M n ↔
      ∀ i (x : L), x ∈ L.grading i → f x ∈ M.grading (i + n) := sorry

/-- Composition of homogeneous right-linear maps adds their degrees. -/
@[stacks 09MN "composition of homogeneous maps"]
abbrev HomogeneousMap.comp {K L M : Right (R := R) (A := A) 𝒜} {m n : ι}
    (g : HomogeneousMap L M m) (f : HomogeneousMap K L n) :
    HomogeneousMap K M (n + m) :=
  GradedModule.HomogeneousMap.comp g f

/-- Homogeneous composition is ordinary composition on the underlying right-linear maps. -/
@[simp]
theorem HomogeneousMap.comp_apply {K L M : Right (R := R) (A := A) 𝒜} {m n : ι}
    (g : HomogeneousMap L M m) (f : HomogeneousMap K L n) (x : K) :
    GradedModule.MapsTo.toLinearMap (HomogeneousMap.comp g f) x =
      GradedModule.MapsTo.toLinearMap g (GradedModule.MapsTo.toLinearMap f x) := sorry

/-- Composition specialized to degree-zero homogeneous maps. -/
@[stacks 09MN "composition of degree-zero homogeneous maps"]
abbrev HomogeneousMap.compZero {K L M : Right (R := R) (A := A) 𝒜}
    (g : HomogeneousMap L M 0) (f : HomogeneousMap K L 0) :
    HomogeneousMap K M 0 :=
  GradedModule.HomogeneousMap.compZero g f

/-- Degree-zero homogeneous composition is ordinary composition on underlying maps. -/
@[simp]
theorem HomogeneousMap.compZero_apply {K L M : Right (R := R) (A := A) 𝒜}
    (g : HomogeneousMap L M 0) (f : HomogeneousMap K L 0) (x : K) :
    GradedModule.MapsTo.toLinearMap (HomogeneousMap.compZero g f) x =
      GradedModule.MapsTo.toLinearMap g (GradedModule.MapsTo.toLinearMap f x) := sorry

/-- Postcomposition by a degree-zero map preserves the degree of a homogeneous map. -/
@[stacks 09MN "degree-zero postcomposition for right graded modules"]
abbrev HomogeneousMap.postcompZero {K L M : Right (R := R) (A := A) 𝒜} {n : ι}
    (g : HomogeneousMap L M 0) (f : HomogeneousMap K L n) :
    HomogeneousMap K M n :=
  GradedModule.HomogeneousMap.postcompZero g f

/-- Degree-zero postcomposition is ordinary composition on underlying maps. -/
@[simp]
theorem HomogeneousMap.postcompZero_apply
    {K L M : Right (R := R) (A := A) 𝒜} {n : ι}
    (g : HomogeneousMap L M 0) (f : HomogeneousMap K L n) (x : K) :
    GradedModule.MapsTo.toLinearMap (HomogeneousMap.postcompZero g f) x =
      GradedModule.MapsTo.toLinearMap g (GradedModule.MapsTo.toLinearMap f x) := sorry

/-- Precomposition by a degree-zero map preserves the degree of a homogeneous map. -/
@[stacks 09MN "degree-zero precomposition for right graded modules"]
abbrev HomogeneousMap.precompZero {K L M : Right (R := R) (A := A) 𝒜} {n : ι}
    (g : HomogeneousMap L M n) (f : HomogeneousMap K L 0) :
    HomogeneousMap K M n :=
  GradedModule.HomogeneousMap.precompZero g f

/-- Degree-zero precomposition is ordinary composition on underlying maps. -/
@[simp]
theorem HomogeneousMap.precompZero_apply
    {K L M : Right (R := R) (A := A) 𝒜} {n : ι}
    (g : HomogeneousMap L M n) (f : HomogeneousMap K L 0) (x : K) :
    GradedModule.MapsTo.toLinearMap (HomogeneousMap.precompZero g f) x =
      GradedModule.MapsTo.toLinearMap g (GradedModule.MapsTo.toLinearMap f x) := sorry

/-- Postcomposition by a fixed degree-zero map is linear on each homogeneous component. -/
@[stacks 09MN "linear degree-zero postcomposition for right graded modules"]
abbrev HomogeneousMap.postcompZeroLinear
    {K L M : Right (R := R) (A := A) 𝒜} {n : ι}
    (g : HomogeneousMap L M 0) :
    HomogeneousMap K L n →ₗ[R] HomogeneousMap K M n :=
  GradedModule.HomogeneousMap.postcompZeroLinear g

/-- Precomposition by a fixed degree-zero map is linear on each homogeneous component. -/
@[stacks 09MN "linear degree-zero precomposition for right graded modules"]
abbrev HomogeneousMap.precompZeroLinear
    {K L M : Right (R := R) (A := A) 𝒜} {n : ι}
    (f : HomogeneousMap K L 0) :
    HomogeneousMap L M n →ₗ[R] HomogeneousMap K M n :=
  GradedModule.HomogeneousMap.precompZeroLinear f

/-- The identity right-linear map is homogeneous of degree zero. -/
@[stacks 09MN "degree-zero identity for right graded modules"]
abbrev HomogeneousMap.id (M : Right (R := R) (A := A) 𝒜) : HomogeneousMap M M 0 :=
  GradedModule.HomogeneousMap.id

/-- Composing a degree-zero homogeneous map with the identity on its source changes nothing. -/
@[simp]
theorem HomogeneousMap.compZero_id {K L : Right (R := R) (A := A) 𝒜}
    (f : HomogeneousMap K L 0) :
    HomogeneousMap.compZero f (HomogeneousMap.id K) = f := sorry

/-- Postcomposing a degree-zero homogeneous map with the identity changes nothing. -/
@[simp]
theorem HomogeneousMap.id_compZero {K L : Right (R := R) (A := A) 𝒜}
    (f : HomogeneousMap K L 0) :
    HomogeneousMap.compZero (HomogeneousMap.id L) f = f := sorry

/-- Degree-zero homogeneous composition is associative. -/
theorem HomogeneousMap.compZero_assoc {K L M N : Right (R := R) (A := A) 𝒜}
    (h : HomogeneousMap M N 0) (g : HomogeneousMap L M 0)
    (f : HomogeneousMap K L 0) :
    HomogeneousMap.compZero (HomogeneousMap.compZero h g) f =
      HomogeneousMap.compZero h (HomogeneousMap.compZero g f) := sorry

/-- Morphisms in the ambient graded category are finite sums of homogeneous maps. -/
@[stacks 09MN "graded Hom as a direct sum of homogeneous maps"]
abbrev Hom (L M : Right (R := R) (A := A) 𝒜) :=
  DirectSum ι (fun n ↦ HomogeneousMap L M n)

/-- Include one homogeneous component into the total graded Hom module. -/
abbrev Hom.of (L M : Right (R := R) (A := A) 𝒜) (n : ι) :
    HomogeneousMap L M n →ₗ[R] Hom L M :=
  DirectSum.lof R ι (fun i ↦ HomogeneousMap L M i) n

/-- Forget the finite homogeneous decomposition and sum the underlying right-linear maps. -/
def Hom.toLinearMap (L M : Right (R := R) (A := A) 𝒜) :
    Hom L M →ₗ[R] (L →ₗ[Aᵐᵒᵖ] M) :=
  DirectSum.toModule R ι (L →ₗ[Aᵐᵒᵖ] M)
    (fun n ↦ (HomogeneousMap L M n).subtype)

/-- On one homogeneous component, `Hom.toLinearMap` returns its underlying map. -/
@[simp]
theorem Hom.toLinearMap_of (L M : Right (R := R) (A := A) 𝒜) (n : ι)
    (f : HomogeneousMap L M n) :
    Hom.toLinearMap L M (Hom.of L M n f) = f := sorry

/-- Postcomposition by a degree-zero map, extended over every homogeneous summand. -/
@[stacks 09MN "postcomposition on total graded Hom"]
def Hom.postcompZero {K L M : Right (R := R) (A := A) 𝒜}
    (g : HomogeneousMap L M 0) : Hom K L →ₗ[R] Hom K M :=
  DirectSum.lmap (fun _ ↦ HomogeneousMap.postcompZeroLinear g)

/-- Precomposition by a degree-zero map, extended over every homogeneous summand. -/
@[stacks 09MN "precomposition on total graded Hom"]
def Hom.precompZero {K L M : Right (R := R) (A := A) 𝒜}
    (f : HomogeneousMap K L 0) : Hom L M →ₗ[R] Hom K M :=
  DirectSum.lmap (fun _ ↦ HomogeneousMap.precompZeroLinear f)

/-- Total postcomposition sends a homogeneous inclusion to the corresponding composite. -/
@[simp]
theorem Hom.postcompZero_of {K L M : Right (R := R) (A := A) 𝒜}
    (g : HomogeneousMap L M 0) (n : ι) (f : HomogeneousMap K L n) :
    Hom.postcompZero g (Hom.of K L n f) =
      Hom.of K M n (HomogeneousMap.postcompZero g f) := sorry

/-- Total precomposition sends a homogeneous inclusion to the corresponding composite. -/
@[simp]
theorem Hom.precompZero_of {K L M : Right (R := R) (A := A) 𝒜}
    (f : HomogeneousMap K L 0) (n : ι) (g : HomogeneousMap L M n) :
    Hom.precompZero f (Hom.of L M n g) =
      Hom.of K M n (HomogeneousMap.precompZero g f) := sorry

/-- Postcomposition by the degree-zero identity is the identity on total Hom. -/
@[simp]
theorem Hom.postcompZero_id (K L : Right (R := R) (A := A) 𝒜) :
    Hom.postcompZero (K := K) (HomogeneousMap.id L) = LinearMap.id := sorry

/-- Precomposition by the degree-zero identity is the identity on total Hom. -/
@[simp]
theorem Hom.precompZero_id (K L : Right (R := R) (A := A) 𝒜) :
    Hom.precompZero (M := L) (HomogeneousMap.id K) = LinearMap.id := sorry

/-- Successive degree-zero postcompositions compose in their evident order. -/
theorem Hom.postcompZero_comp {K L M N : Right (R := R) (A := A) 𝒜}
    (h : HomogeneousMap M N 0) (g : HomogeneousMap L M 0) :
    Hom.postcompZero (K := K) (HomogeneousMap.compZero h g) =
      (Hom.postcompZero h).comp (Hom.postcompZero g) := sorry

/-- Successive degree-zero precompositions compose contravariantly. -/
theorem Hom.precompZero_comp {K L M N : Right (R := R) (A := A) 𝒜}
    (g : HomogeneousMap L M 0) (f : HomogeneousMap K L 0) :
    Hom.precompZero (M := N) (HomogeneousMap.compZero g f) =
      (Hom.precompZero f).comp (Hom.precompZero g) := sorry

/-- Degree-zero precomposition and postcomposition commute on total Hom. -/
theorem Hom.postcompZero_precompZero
    {K L M N : Right (R := R) (A := A) 𝒜}
    (g : HomogeneousMap M N 0) (f : HomogeneousMap K L 0) :
    (Hom.postcompZero g).comp (Hom.precompZero f) =
      (Hom.precompZero f).comp (Hom.postcompZero g) := sorry

/-- Composition by a fixed homogeneous map, extended linearly over the source Hom direct sum. -/
def HomogeneousMap.postcomp {K L M : Right (R := R) (A := A) 𝒜} {m : ι}
    (g : HomogeneousMap L M m) : Hom K L →ₗ[R] Hom K M :=
  DirectSum.toModule R ι (Hom K M) (fun n ↦
    (Hom.of K M (n + m)).comp
      ({ toFun := fun f ↦ HomogeneousMap.comp g f
         map_add' := sorry
         map_smul' := sorry } :
        HomogeneousMap K L n →ₗ[R] HomogeneousMap K M (n + m)))

/-- Bilinear composition on the total graded Hom modules. -/
def Hom.compLinear {K L M : Right (R := R) (A := A) 𝒜} :
    Hom L M →ₗ[R] Hom K L →ₗ[R] Hom K M :=
  DirectSum.toModule R ι (Hom K L →ₗ[R] Hom K M) (fun _ ↦
    { toFun := HomogeneousMap.postcomp
      map_add' := sorry
      map_smul' := sorry })

/-- Composition on total graded Hom modules. -/
def Hom.comp {K L M : Right (R := R) (A := A) 𝒜}
    (g : Hom L M) (f : Hom K L) : Hom K M :=
  Hom.compLinear g f

/-- The identity in the total Hom module is the degree-zero homogeneous identity. -/
def Hom.id (M : Right (R := R) (A := A) 𝒜) : Hom M M :=
  Hom.of M M 0 (HomogeneousMap.id M)

/-- Right graded modules form a category whose morphisms are finite sums of homogeneous maps. -/
instance instCategory : Category (Right (R := R) (A := A) 𝒜) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The graded-module category is preadditive. -/
instance instPreadditive : Preadditive (Right (R := R) (A := A) 𝒜) where
  homGroup := fun X Y ↦ inferInstanceAs (AddCommGroup (Hom X Y))
  add_comp := sorry
  comp_add := sorry

/-- The graded-module category is `R`-linear. -/
instance instLinear : Linear R (Right (R := R) (A := A) 𝒜) where
  homModule := fun X Y ↦ inferInstanceAs (Module R (Hom X Y))
  smul_comp := sorry
  comp_smul := sorry

/-- The degree-`n` submodule of the total graded Hom module. -/
def homDegree (L M : Right (R := R) (A := A) 𝒜) (n : ι) : Submodule R (Hom L M) :=
  (Hom.of L M n).range

/-- The canonical inclusion of homogeneous maps into the corresponding Hom-degree submodule. -/
def homogeneousMapToDegree (L M : Right (R := R) (A := A) 𝒜) (n : ι) :
    HomogeneousMap L M n →ₗ[R] homDegree L M n where
  toFun f := ⟨Hom.of L M n f, ⟨f, rfl⟩⟩
  map_add' := sorry
  map_smul' := sorry

/-- Homogeneous maps identify with their summands in the total graded Hom module. -/
def homogeneousMapEquivDegree (L M : Right (R := R) (A := A) 𝒜) (n : ι) :
    HomogeneousMap L M n ≃ₗ[R] homDegree L M n where
  toFun := homogeneousMapToDegree L M n
  invFun f := DirectSum.component R ι (fun i ↦ HomogeneousMap L M i) n f.1
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- Decompose a total graded Hom into its canonical embedded homogeneous summands. -/
def homDecompose (L M : Right (R := R) (A := A) 𝒜) :
    Hom L M →ₗ[R] DirectSum ι (fun n ↦ homDegree L M n) :=
  DirectSum.toModule R ι (DirectSum ι (fun n ↦ homDegree L M n)) (fun n ↦
    (DirectSum.lof R ι (fun i ↦ homDegree L M i) n).comp
      (homogeneousMapEquivDegree L M n).toLinearMap)

/-- The degree submodules give the canonical direct-sum decomposition of every Hom module. -/
instance instHomDecomposition (L M : Right (R := R) (A := A) 𝒜) :
    DirectSum.Decomposition (homDegree L M) :=
  DirectSum.Decomposition.ofLinearMap (homDegree L M) (homDecompose L M) sorry sorry

/-- Right graded modules and finite sums of homogeneous maps form a graded `R`-linear category. -/
@[stacks 09MN "graded category of right graded modules"]
instance gradedCategory : GradedCategory R (Right (R := R) (A := A) 𝒜) ι where
  homDegree := homDegree
  homDecomposition := fun L M ↦ instHomDecomposition (𝒜 := 𝒜) L M
  id_mem_homDegree_zero := sorry
  comp_mem := sorry

/-- The ordinary category of right graded modules is the degree-zero category of the ambient
graded category. -/
@[stacks 09MN "degree-zero category of right graded modules"]
abbrev DegreeZero :=
  GradedCategory.DegreeZero (R := R) (Right (R := R) (A := A) 𝒜) ι

/-- A degree-zero morphism is exactly a right-linear map preserving every homogeneous piece. -/
@[stacks 09MN "degree-zero morphisms of right graded modules"]
def degreeZeroHomEquiv (L M : Right (R := R) (A := A) 𝒜) :
    HomogeneousMap L M 0 ≃ₗ[R]
      ((⟨L⟩ : GradedCategory.DegreeZero (R := R)
          (Right (R := R) (A := A) 𝒜) ι) ⟶
        (⟨M⟩ : GradedCategory.DegreeZero (R := R)
          (Right (R := R) (A := A) 𝒜) ι)) where
  toFun f := ⟨Hom.of L M 0 f, ⟨f, rfl⟩⟩
  invFun f := DirectSum.component R ι (fun i ↦ HomogeneousMap L M i) 0 f.hom
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- The ambient total morphism underlying a degree-zero homogeneous map is its canonical direct
sum inclusion. -/
@[simp]
theorem degreeZeroHomEquiv_hom (L M : Right (R := R) (A := A) 𝒜)
    (f : HomogeneousMap L M 0) :
    (degreeZeroHomEquiv L M f).hom = Hom.of L M 0 f := sorry

end Right

end GradedModule
