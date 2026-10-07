module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedRing
public import Mathlib.Topology.Algebra.ClopenNhdofOne

@[expose] public section

open CategoryTheory CategoryTheory.Action.ModuleCat
open scoped MonoidAlgebra

noncomputable section

universe u v

namespace NoncommPointwiseCompletedAction

variable (Λ : Type u) [Ring Λ]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual open stabilizer of this vector. -/
def stabilizer (M : DiscreteModuleCat Λ G) (m : M.obj.V) : OpenSubgroup G :=
  ⟨MulAction.stabilizer G m, M.property m⟩

/-- The normal core is open because an open subgroup of a compact group has
finite index. This is a pointwise construction, not a whole-action kernel. -/
def core [CompactSpace G] (M : DiscreteModuleCat Λ G) (m : M.obj.V) :
    OpenNormalSubgroup G := by
  let H := stabilizer Λ G M m
  -- Local instance justification (proof-local temporary data): the stabilizer of this vector has finite index, supplying openness of its normal core.
  letI : Subgroup.FiniteIndex H.toSubgroup := H.finiteIndex_of_finite_quotient
  exact
    { toOpenSubgroup :=
        { toSubgroup := H.toSubgroup.normalCore
          isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex _
            (H.toSubgroup.normalCore_isClosed H.isClosed) }
      isNormal' := inferInstance }

/-- The normal core of a vector stabilizer fixes that vector. -/
theorem core_fixes [CompactSpace G] (M : DiscreteModuleCat Λ G) (m : M.obj.V)
    (g : G) (hg : g ∈ core Λ G M m) : (M.obj.ρ g).hom m = m := by
  exact (stabilizer Λ G M m).toSubgroup.normalCore_le hg

/-- The finite-quotient orbit value. It is independent of the representative
whenever N fixes m; that condition is recorded in the following theorem. -/
def orbit (M : DiscreteModuleCat Λ G) (N : OpenNormalSubgroup G)
    (m : M.obj.V) (q : G ⧸ N.toSubgroup) : M.obj.V :=
  (M.obj.ρ (Quotient.out q)).hom m

/-- A quotient orbit value recovers the translate when the subgroup fixes the vector. -/
theorem orbit_mk (M : DiscreteModuleCat Λ G) (N : OpenNormalSubgroup G)
    (m : M.obj.V) (h : ∀ g ∈ N, (M.obj.ρ g).hom m = m) (g : G) :
    orbit Λ G M N m (QuotientGroup.mk g) = (M.obj.ρ g).hom m := by
  sorry

/-- Apply a group-algebra coefficient at a normal subgroup fixing m. -/
def atLevel (M : DiscreteModuleCat Λ G) (N : OpenNormalSubgroup G)
    (r : NoncommCompletedRing.Obj Λ G) (m : M.obj.V) : M.obj.V :=
  (NoncommCompletedRing.projection Λ G N r).coeff.sum fun q a ↦ a • orbit Λ G M N m q

/-- Refinement does not change the orbit sum, by compatibility of the actual
completed-ring family and invariance of m. -/
theorem atLevel_refine (M : DiscreteModuleCat Λ G)
    (N K : OpenNormalSubgroup G) (hKN : K ≤ N)
    (r : NoncommCompletedRing.Obj Λ G) (m : M.obj.V)
    (hN : ∀ g ∈ N, (M.obj.ρ g).hom m = m) :
    atLevel Λ G M K r m = atLevel Λ G M N r m := by
  sorry

/-- Two normal subgroups fixing m have the common refinement N ∩ K. -/
theorem atLevel_independent (M : DiscreteModuleCat Λ G)
    (N K : OpenNormalSubgroup G) (r : NoncommCompletedRing.Obj Λ G) (m : M.obj.V)
    (hN : ∀ g ∈ N, (M.obj.ρ g).hom m = m)
    (hK : ∀ g ∈ K, (M.obj.ρ g).hom m = m) :
    atLevel Λ G M N r m = atLevel Λ G M K r m := by
  exact (atLevel_refine Λ G M N (N ⊓ K) inf_le_left r m hN).symm.trans
    (atLevel_refine Λ G M K (N ⊓ K) inf_le_right r m hK)

/-- Evaluate a completed scalar at the normal core of the vector's stabilizer. -/
def scalar [CompactSpace G] (M : DiscreteModuleCat Λ G)
    (r : NoncommCompletedRing.Obj Λ G) (m : M.obj.V) : M.obj.V :=
  atLevel Λ G M (core Λ G M m) r m

/-- Scalar evaluation can use any open normal subgroup fixing the vector. -/
theorem scalar_atLevel [CompactSpace G] (M : DiscreteModuleCat Λ G)
    (N : OpenNormalSubgroup G) (r : NoncommCompletedRing.Obj Λ G) (m : M.obj.V)
    (hN : ∀ g ∈ N, (M.obj.ρ g).hom m = m) :
    scalar Λ G M r m = atLevel Λ G M N r m :=
  atLevel_independent Λ G M _ N r m (core_fixes Λ G M m) hN

/-- The underlying vectors, viewed with their specified pointwise completed action. -/
def Carrier (M : DiscreteModuleCat Λ G) := M.obj.V

/-- The carrier keeps the original additive group. -/
instance (M : DiscreteModuleCat Λ G) : AddCommGroup (Carrier Λ G M) :=
  inferInstanceAs (AddCommGroup M.obj.V)

/-- The module laws follow by a common normal refinement. For multiplication,
normality ensures that a subgroup fixing m fixes its entire orbit span. -/
instance [CompactSpace G] (M : DiscreteModuleCat Λ G) :
    Module (NoncommCompletedRing.Obj Λ G) (Carrier Λ G M) where
  smul := scalar Λ G M
  one_smul := by sorry
  mul_smul := by sorry
  smul_zero := by sorry
  smul_add := by sorry
  add_smul := by sorry
  zero_smul := by sorry

/-- Bundle the pointwise completed action as an algebraic module. -/
def module [CompactSpace G] (M : DiscreteModuleCat Λ G) :
    ModuleCat.{max u v} (NoncommCompletedRing.Obj Λ G) :=
  ModuleCat.of (NoncommCompletedRing.Obj Λ G) (Carrier Λ G M)

/-- Equivariant maps commute with the pointwise completed scalar action. -/
theorem scalar_naturality [CompactSpace G] {M N : DiscreteModuleCat Λ G}
    (f : M ⟶ N) (r : NoncommCompletedRing.Obj Λ G) (m : M.obj.V) :
    f.hom.hom (scalar Λ G M r m) = scalar Λ G N r (f.hom.hom m) := by
  sorry

/-- Extend an equivariant map without changing its underlying function. -/
def map [CompactSpace G] {M N : DiscreteModuleCat Λ G} (f : M ⟶ N) :
    module Λ G M ⟶ module Λ G N :=
  ModuleCat.ofHom
    { toFun := fun m ↦ f.hom.hom m
      map_add' := fun m n ↦ f.hom.hom.hom.map_add m n
      map_smul' := scalar_naturality Λ G f }

/-- Extend discrete continuous representations to pointwise completed modules. -/
def functor [CompactSpace G] :
    DiscreteModuleCat Λ G ⥤ ModuleCat.{max u v} (NoncommCompletedRing.Obj Λ G) where
  obj := module Λ G
  map := map Λ G
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Compatibility with the original coefficient-ring action. -/
theorem scalar_ofScalar [CompactSpace G] (M : DiscreteModuleCat Λ G)
    (a : Λ) (m : M.obj.V) :
    scalar Λ G M (NoncommCompletedRing.ofScalar Λ G a) m = a • m := by
  sorry

/-- The actual Dirac family of a group element. -/
def dirac (g : G) : NoncommCompletedRing.Obj Λ G :=
  ⟨fun N ↦ MonoidAlgebra.single (QuotientGroup.mk g : G ⧸ N.toSubgroup) 1, by sorry⟩

/-- The new completed action recovers the given group action. -/
theorem scalar_dirac [CompactSpace G] (M : DiscreteModuleCat Λ G)
    (g : G) (m : M.obj.V) : scalar Λ G M (dirac Λ G g) m = (M.obj.ρ g).hom m := by
  sorry

/-- Each vector is killed by the kernel of one finite-quotient projection.
This is the requisite continuity property for the inverse-limit ring topology
when the coefficient ring and module carriers are discrete. -/
theorem projection_kernel_annihilates [CompactSpace G] (M : DiscreteModuleCat Λ G)
    (m : M.obj.V) (r : NoncommCompletedRing.Obj Λ G)
    (h : NoncommCompletedRing.projection Λ G (core Λ G M m) r = 0) :
    scalar Λ G M r m = 0 := by
  simp [scalar, atLevel, h]

/-- A completed-linear map recovers a Λ-linear equivariant map through scalar
and Dirac recovery. This uses exactly the original underlying function. -/
def unmap [CompactSpace G] {M N : DiscreteModuleCat Λ G}
    (f : module Λ G M ⟶ module Λ G N) : M ⟶ N :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun m ↦ f.hom m
          map_add' := fun m n ↦ f.hom.map_add m n
          map_smul' := by sorry }
      comm := by sorry }

/-- Translation is fully faithful; it does not identify all algebraic completed
modules with continuous representations. -/
def homEquiv [CompactSpace G] (M N : DiscreteModuleCat Λ G) :
    (M ⟶ N) ≃ (module Λ G M ⟶ module Λ G N) where
  toFun := map Λ G
  invFun := unmap Λ G
  left_inv := by intro f; rfl
  right_inv := by intro f; rfl

end NoncommPointwiseCompletedAction
