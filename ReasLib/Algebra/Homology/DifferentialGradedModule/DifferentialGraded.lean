/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Submodule.Basic
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift
public import ReasLib.Algebra.Category.DifferentialGraded

/-!
# Differential Graded Enrichment of Differential Graded Modules

For a cochain differential graded algebra `A`, this leaf constructs the
`R`-linear differential graded category of right differential graded
`A`-modules.  The lower `DifferentialGradedCategory` API owns the abstract
enrichment; this file supplies the concrete graded Hom complex of modules.
-/

@[expose] public section

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

noncomputable section

universe u v

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-- Reassociation of the target degree in the right linearity condition for a homogeneous map. -/
theorem gradedHom_smul_index (n m k : ℤ) : (n + k) + m = (n + m) + k := sorry

/-- Reassociation of the left term in the differential of a graded Hom. -/
theorem gradedHom_differential_left_index (n k : ℤ) : (n + k) + 1 = n + (k + 1) := sorry

/-- Reassociation of the right term in the differential of a graded Hom. -/
theorem gradedHom_differential_right_index (n k : ℤ) : (n + 1) + k = n + (k + 1) := sorry

/-- Reassociation of the target degree of a composite of homogeneous maps. -/
theorem gradedHom_comp_index (n i j : ℤ) : (n + i) + j = n + (i + j) := sorry

/-- The submodule of degree-`k` families of right-`A`-linear maps. -/
@[stacks 09LC "graded Hom submodule for differential graded modules"]
def gradedHomSubmodule
    (A : CochainDGAlgebra R) (L M : DifferentialGradedModule A) (k : ℤ) :
    Submodule R (∀ n : ℤ, L.X n →ₗ[R] M.X (n + k)) where
  carrier := { f | ∀ n m (x : L.X n) (a : A.X m),
    f (n + m) (L.smul n m x a) =
      cast (congrArg (fun t : ℤ ↦ (M.X t : Type _)) (gradedHom_smul_index n m k))
        (M.smul (n + k) m (f n x) a) }
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- The degree-`k` homogeneous right-`A`-linear maps between two differential graded modules. -/
abbrev GradedHom (A : CochainDGAlgebra R)
    (L M : DifferentialGradedModule A) (k : ℤ) : Type _ :=
  gradedHomSubmodule A L M k

/-- A homogeneous graded Hom can be applied degreewise to its underlying linear maps. -/
instance instCoeFunGradedHom {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} {k : ℤ} :
    CoeFun (GradedHom A L M k) (fun _ ↦ ∀ n : ℤ, L.X n →ₗ[R] M.X (n + k)) where
  coe f := f.1

/-- Coercion of a homogeneous graded Hom recovers its family of linear maps. -/
@[simp]
theorem gradedHom_coe {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} {k : ℤ} (f : GradedHom A L M k) :
    ((f : ∀ n : ℤ, L.X n →ₗ[R] M.X (n + k))) = f.1 := sorry

/-- Evaluating a homogeneous graded Hom uses its underlying degreewise linear map. -/
@[simp]
theorem gradedHom_coe_apply {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} {k : ℤ}
    (f : GradedHom A L M k) (n : ℤ) (x : L.X n) : f n x = f.1 n x := sorry

/-- Homogeneous graded maps are determined by their values in every degree. -/
@[ext]
theorem gradedHom_ext {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} {k : ℤ}
    {f g : GradedHom A L M k}
    (h : ∀ n : ℤ, ∀ x : L.X n, f n x = g n x) : f = g := sorry

/-- A homogeneous graded Hom is right-`A`-linear in every bidegree. -/
@[simp]
theorem gradedHom_comm_smul {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} {k : ℤ}
    (f : GradedHom A L M k) (n m : ℤ) (x : L.X n) (a : A.X m) :
    f (n + m) (L.smul n m x a) =
      cast (congrArg (fun t : ℤ ↦ (M.X t : Type _)) (gradedHom_smul_index n m k))
        (M.smul (n + k) m (f n x) a) := sorry

/-- The differential on the graded Hom object of differential graded modules. -/
@[stacks 09LC "graded Hom differential for differential graded modules"]
def gradedHomDifferential {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} (k : ℤ) :
    GradedHom A L M k → GradedHom A L M (k + 1) :=
  fun f ↦
    ⟨fun n ↦
      ModuleCat.castLinearMap
          (congrArg M.X (gradedHom_differential_left_index n k))
          ((M.d (n + k)).comp (f n)) -
        (k.negOnePow : R) •
          ModuleCat.castLinearMap
            (congrArg M.X (gradedHom_differential_right_index n k))
            ((f (n + 1)).comp (L.d n)),
      sorry⟩

/-- The degree-`n` component of the graded-Hom differential is
`d_M ∘ f - (-1)^k f ∘ d_L`, after the required reindexings. -/
@[simp]
theorem gradedHomDifferential_apply {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} (k : ℤ)
    (f : GradedHom A L M k) (n : ℤ) :
    gradedHomDifferential k f n =
      ModuleCat.castLinearMap
          (congrArg M.X (gradedHom_differential_left_index n k))
          ((M.d (n + k)).comp (f n)) -
        (k.negOnePow : R) •
          ModuleCat.castLinearMap
            (congrArg M.X (gradedHom_differential_right_index n k))
            ((f (n + 1)).comp (L.d n)) := sorry

/-- The identity element in degree zero of the graded Hom object. -/
@[stacks 09LC "graded Hom identity for differential graded modules"]
def gradedHomId {A : CochainDGAlgebra R}
    (L : DifferentialGradedModule A) : GradedHom A L L 0 :=
  ⟨fun n ↦
      ModuleCat.castLinearMap (congrArg L.X (add_zero n).symm) LinearMap.id,
    sorry⟩

/-- The degreewise action of the graded-Hom identity is the identity linear map with its canonical
degree-zero reindexing. -/
@[simp]
theorem gradedHomId_apply {A : CochainDGAlgebra R}
    (L : DifferentialGradedModule A) (n : ℤ) (x : L.X n) :
    gradedHomId L n x =
      ModuleCat.castLinearMap (congrArg L.X (add_zero n).symm) LinearMap.id x := sorry

/-- Homogeneous composition of right-`A`-linear graded maps. -/
@[stacks 09LC "graded Hom composition for differential graded modules"]
def gradedHomComp {A : CochainDGAlgebra R}
    {K L M : DifferentialGradedModule A} {i j : ℤ}
    (g : GradedHom A L M j) (f : GradedHom A K L i) : GradedHom A K M (i + j) :=
  ⟨fun n ↦
      ModuleCat.castLinearMap
        (congrArg M.X (gradedHom_comp_index n i j))
        ((g (n + i)).comp (f n)),
    sorry⟩

/-- The degreewise action of homogeneous graded composition. -/
@[simp]
theorem gradedHomComp_apply {A : CochainDGAlgebra R}
    {K L M : DifferentialGradedModule A} {i j : ℤ}
    (g : GradedHom A L M j) (f : GradedHom A K L i) (n : ℤ) (x : K.X n) :
    gradedHomComp g f n x =
      ModuleCat.castLinearMap (congrArg M.X (gradedHom_comp_index n i j))
        ((g (n + i)).comp (f n)) x := sorry

/-- Example 22.26.8 (Differential graded category of differential graded modules): right
differential graded `A`-modules form the differential graded category whose Hom objects are
`GradedHom`, with the standard Hom differential and homogeneous composition. -/
@[stacks 09LC, reducible]
instance differentialGradedCategory (A : CochainDGAlgebra R) :
    DifferentialGradedCategory R (DifferentialGradedModule A) where
  Hom L M k := GradedHom A L M k
  homAddCommGroup := fun _ _ _ ↦ inferInstance
  homModule := fun _ _ _ ↦ inferInstance
  d := fun k f ↦ gradedHomDifferential k f
  id := gradedHomId
  comp := fun {K L M} {i j} g f ↦ gradedHomComp g f
  d_sq := sorry
  d_id := sorry
  id_comp_hom := sorry
  comp_id_hom := sorry
  comp_assoc := sorry
  comp_add_left := sorry
  comp_add_right := sorry
  comp_smul_left := sorry
  comp_smul_right := sorry
  d_add := sorry
  d_smul := sorry
  d_comp := sorry

/-- The family of degreewise linear maps underlying an enriched morphism of differential
graded modules. -/
def dgHomFamily {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} {k : ℤ} (f : L ⟶[k] M) :
    ∀ n : ℤ, L.X n →ₗ[R] M.X (n + k) :=
  (f : GradedHom A L M k).1

/-- An enriched morphism of differential graded modules acts degreewise on homogeneous
elements. -/
instance instCoeFunDgHom {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} {k : ℤ} :
    CoeFun (L ⟶[k] M) (fun _ ↦ ∀ n : ℤ, L.X n →ₗ[R] M.X (n + k)) where
  coe := dgHomFamily

/-- Evaluating an enriched morphism uses its underlying family of degreewise linear maps. -/
@[simp]
theorem dgHom_apply {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} {k : ℤ}
    (f : L ⟶[k] M) (n : ℤ) (x : L.X n) :
    f n x = dgHomFamily f n x := sorry

/-- The Hom object in the DG category of differential graded modules is `GradedHom`. -/
@[simp]
theorem differentialGradedCategory_hom (A : CochainDGAlgebra R)
    (L M : DifferentialGradedModule A) (k : ℤ) :
    (L ⟶[k] M) = GradedHom A L M k := sorry

/-- The differential in the DG category of differential graded modules is `gradedHomDifferential`.
-/
@[simp]
theorem differentialGradedCategory_d {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} (k : ℤ)
    (f : GradedHom A L M k) :
    (differentialGradedCategory A).d k f = gradedHomDifferential k f := sorry

/-- The degree-zero identity in the DG category of differential graded modules is `gradedHomId`.
-/
@[simp]
theorem differentialGradedCategory_id {A : CochainDGAlgebra R}
    (L : DifferentialGradedModule A) :
    (differentialGradedCategory A).id L = gradedHomId L := sorry

/-- Composition in the DG category of differential graded modules is `gradedHomComp`. -/
@[simp]
theorem differentialGradedCategory_comp {A : CochainDGAlgebra R}
    {K L M : DifferentialGradedModule A} {i j : ℤ}
    (g : GradedHom A L M j) (f : GradedHom A K L i) :
    (differentialGradedCategory A).comp g f = gradedHomComp g f := sorry

/-- The closed degree-`k` homogeneous maps in the graded Hom object. -/
@[stacks 09LC "closed graded Hom maps"]
abbrev ClosedGradedHom (A : CochainDGAlgebra R)
    (L M : DifferentialGradedModule A) (k : ℤ) : Type _ :=
  { f : GradedHom A L M k | gradedHomDifferential k f = 0 }

/-- A closed homogeneous graded map is killed by the graded-Hom differential. -/
@[simp]
theorem closedGradedHom_closed {A : CochainDGAlgebra R}
    {L M : DifferentialGradedModule A} {k : ℤ}
    (f : ClosedGradedHom A L M k) : gradedHomDifferential k f.1 = 0 := sorry

/-- Closed degree-`k` homogeneous maps are equivalent to DG-module maps into the shift by `k`. -/
@[stacks 09LC "closed graded Hom and shifted module equivalence"]
def closedGradedHomEquivShiftHom (A : CochainDGAlgebra R)
    (L M : DifferentialGradedModule A) (k : ℤ) :
    ClosedGradedHom A L M k ≃ (L ⟶ M[k]) where
  toFun f :=
    { hom := fun n ↦
        ModuleCat.castLinearMap (DifferentialGradedModule.shift_X M k n).symm (f.1 n)
      comm_d := sorry
      comm_smul := sorry }
  invFun g :=
    ⟨⟨fun n ↦
          ModuleCat.castLinearMap (DifferentialGradedModule.shift_X M k n) (g.hom n),
        sorry⟩,
      sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- The forward shift equivalence is the canonical reindexing of degreewise linear maps. -/
@[simp, stacks 09LC "closed graded Hom shift equivalence forward map"]
theorem closedGradedHomEquivShiftHom_hom (A : CochainDGAlgebra R)
    (L M : DifferentialGradedModule A) (k : ℤ)
    (f : ClosedGradedHom A L M k) (n : ℤ) :
    (closedGradedHomEquivShiftHom A L M k f).hom n =
      ModuleCat.castLinearMap (DifferentialGradedModule.shift_X M k n).symm (f.1 n) := sorry

/-- The inverse shift equivalence recovers a homogeneous map from a shifted DG-module morphism. -/
@[simp, stacks 09LC "closed graded Hom shift equivalence inverse map"]
theorem closedGradedHomEquivShiftHom_symm_apply (A : CochainDGAlgebra R)
    (L M : DifferentialGradedModule A) (k : ℤ)
    (g : L ⟶ M[k]) (n : ℤ) :
    (((closedGradedHomEquivShiftHom A L M k).symm g).1 : GradedHom A L M k) n =
      ModuleCat.castLinearMap (DifferentialGradedModule.shift_X M k n) (g.hom n) := sorry

end DifferentialGradedModule
