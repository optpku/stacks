/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.Topology.Algebra.OpenNormalSubgroup

/-!
# Completed group rings and augmentation

This leaf owns `Λ[[G]]` as the compatible families in group algebras `Λ[G ⧸ N]`
over open normal subgroups, together with scalar inclusion and augmentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Action.ModuleCat
open scoped MonoidAlgebra

noncomputable section

universe u v

variable (Λ : Type u) [CommRing Λ]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Transition maps of finite group algebras along inclusions of open normal subgroups. -/
def finiteQuotientGroupAlgebraMap {N N' : OpenNormalSubgroup G} (h : N ≤ N') :
    MonoidAlgebra Λ (G ⧸ N.toSubgroup) →+* MonoidAlgebra Λ (G ⧸ N'.toSubgroup) :=
  MonoidAlgebra.mapDomainRingHom Λ
    (QuotientGroup.map N.toSubgroup N'.toSubgroup (MonoidHom.id G) sorry)

/-- Compatibility of a family of finite group-algebra elements with the inverse system
of open normal quotients. -/
def CompletedGroupRing.IsCompatible
    (f : ∀ N : OpenNormalSubgroup G, MonoidAlgebra Λ (G ⧸ N.toSubgroup)) : Prop :=
  ∀ ⦃N N' : OpenNormalSubgroup G⦄ (h : N ≤ N'),
    finiteQuotientGroupAlgebraMap Λ G h (f N) = f N'

/-- The completed group ring `Λ[[G]]`, realized as compatible families in the inverse
limit of finite group algebras of open normal quotients. -/
def completedGroupRing : Type (max u v) :=
  { f : ∀ N : OpenNormalSubgroup G, MonoidAlgebra Λ (G ⧸ N.toSubgroup) //
    CompletedGroupRing.IsCompatible Λ G f }

namespace completedGroupRing

/-- The zero family in the completed group ring. -/
instance instZero : Zero (completedGroupRing Λ G) :=
  ⟨⟨fun _ ↦ 0, sorry⟩⟩

/-- The unit family in the completed group ring. -/
instance instOne : One (completedGroupRing Λ G) :=
  ⟨⟨fun _ ↦ 1, sorry⟩⟩

/-- Pointwise addition of compatible families. -/
instance instAdd : Add (completedGroupRing Λ G) :=
  ⟨fun a b ↦ ⟨fun N ↦ a.val N + b.val N, sorry⟩⟩

/-- Pointwise multiplication of compatible families. -/
instance instMul : Mul (completedGroupRing Λ G) :=
  ⟨fun a b ↦ ⟨fun N ↦ a.val N * b.val N, sorry⟩⟩

/-- Pointwise negation of compatible families. -/
instance instNeg : Neg (completedGroupRing Λ G) :=
  ⟨fun a ↦ ⟨fun N ↦ -a.val N, sorry⟩⟩

/-- Pointwise subtraction of compatible families. -/
instance instSub : Sub (completedGroupRing Λ G) :=
  ⟨fun a b ↦ ⟨fun N ↦ a.val N - b.val N, sorry⟩⟩

/-- Natural-number scalar multiplication on compatible families. -/
instance instSMulNat : SMul ℕ (completedGroupRing Λ G) :=
  ⟨fun n a ↦ ⟨fun N ↦ n • a.val N, sorry⟩⟩

/-- Integer scalar multiplication on compatible families. -/
instance instSMulInt : SMul ℤ (completedGroupRing Λ G) :=
  ⟨fun n a ↦ ⟨fun N ↦ n • a.val N, sorry⟩⟩

/-- Natural-number powers of compatible families. -/
instance instPowNat : Pow (completedGroupRing Λ G) ℕ :=
  ⟨fun a n ↦ ⟨fun N ↦ a.val N ^ n, sorry⟩⟩

/-- Coercion of natural numbers into the completed group ring. -/
instance instNatCast : NatCast (completedGroupRing Λ G) :=
  ⟨fun n ↦ ⟨fun _ ↦ n, sorry⟩⟩

/-- Coercion of integers into the completed group ring. -/
instance instIntCast : IntCast (completedGroupRing Λ G) :=
  ⟨fun n ↦ ⟨fun _ ↦ n, sorry⟩⟩

/-- The product of the finite group algebras carries a ring structure. -/
instance instPiRing :
    Ring (∀ N : OpenNormalSubgroup G, MonoidAlgebra Λ (G ⧸ N.toSubgroup)) :=
  Pi.ring

/-- The completed group ring is a ring, as a subring of the product of finite group algebras. -/
instance instRing : Ring (completedGroupRing Λ G) :=
  Function.Injective.ring (fun a : completedGroupRing Λ G ↦ a.val)
    Subtype.val_injective sorry sorry sorry sorry sorry sorry sorry sorry sorry sorry sorry

/-- The image of an open normal subgroup along a group isomorphism, with openness
deferred. -/
def openNormalSubgroupMapMulEquiv {G' : Type v} [Group G'] [TopologicalSpace G']
    (e : G ≃* G') (N : OpenNormalSubgroup G) : OpenNormalSubgroup G' where
  toOpenSubgroup :=
    { toSubgroup := N.toSubgroup.map e.toMonoidHom
      isOpen' := sorry }
  isNormal' := sorry

/-- Unfolding of the image of an open normal subgroup along a group isomorphism. -/
theorem openNormalSubgroupMapMulEquiv_toSubgroup {G' : Type v} [Group G']
    [TopologicalSpace G'] (e : G ≃* G') (N : OpenNormalSubgroup G) :
    (openNormalSubgroupMapMulEquiv (G := G) e N).toSubgroup =
      N.toSubgroup.map e.toMonoidHom :=
  sorry

/-- The completed group ring isomorphism induced by a group isomorphism. -/
def congrMulEquiv {G' : Type v} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    (e : G ≃* G') : completedGroupRing Λ G ≃+* completedGroupRing Λ G' where
  toFun f :=
    ⟨fun N =>
      MonoidAlgebra.mapDomainRingHom Λ
        (QuotientGroup.map
          (openNormalSubgroupMapMulEquiv (G := G') e.symm N).toSubgroup N.toSubgroup
          e.toMonoidHom sorry)
        (f.val (openNormalSubgroupMapMulEquiv (G := G') e.symm N)),
      sorry⟩
  invFun g :=
    ⟨fun N =>
      MonoidAlgebra.mapDomainRingHom Λ
        (QuotientGroup.map
          (openNormalSubgroupMapMulEquiv (G := G) e N).toSubgroup N.toSubgroup
          e.symm.toMonoidHom sorry)
        (g.val (openNormalSubgroupMapMulEquiv (G := G) e N)),
      sorry⟩
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  map_add' := sorry

/-- Unfolding of `congrMulEquiv` on compatible families. -/
theorem congrMulEquiv_apply {G' : Type v} [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] (e : G ≃* G') (f : completedGroupRing Λ G)
    (N : OpenNormalSubgroup G') :
    (congrMulEquiv (Λ := Λ) (G := G) e f).val N =
      MonoidAlgebra.mapDomainRingHom Λ
        (QuotientGroup.map
          (openNormalSubgroupMapMulEquiv (G := G') e.symm N).toSubgroup N.toSubgroup
          e.toMonoidHom sorry)
        (f.val (openNormalSubgroupMapMulEquiv (G := G') e.symm N)) :=
  sorry

/-- Projection from the completed group ring onto the finite group algebra of an open
normal quotient. -/
def π (N : OpenNormalSubgroup G) :
    completedGroupRing Λ G →+* MonoidAlgebra Λ (G ⧸ N.toSubgroup) where
  toFun f := f.val N
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The structure map `Λ →+* Λ[[G]]`, sending a scalar to the constant family of scalars. -/
def ofScalar : Λ →+* completedGroupRing Λ G where
  toFun r := ⟨fun _ ↦ algebraMap Λ _ r, sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The augmentation `Λ[[G]] →+* Λ`, as the coefficient of the identity in the trivial
quotient `G ⧸ G`. -/
def augmentation : completedGroupRing Λ G →+* Λ where
  toFun f := (π Λ G (⊤ : OpenNormalSubgroup G) f).coeff 1
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

end completedGroupRing

/-- The completed group ring isomorphism induced by a group isomorphism. -/
def completedGroupRingCongrMulEquiv {G' : Type v} [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] (e : G ≃* G') :
    completedGroupRing Λ G ≃+* completedGroupRing Λ G' :=
  completedGroupRing.congrMulEquiv (Λ := Λ) (G := G) e

/-- Unfolding of `completedGroupRingCongrMulEquiv` as the namespaced group-isomorphism action. -/
theorem completedGroupRingCongrMulEquiv_spec {G' : Type v} [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (e : G ≃* G') :
    completedGroupRingCongrMulEquiv (Λ := Λ) (G := G) e =
      completedGroupRing.congrMulEquiv (Λ := Λ) (G := G) e :=
  rfl

/-- The trivial `Λ[[G]]`-module `Λ`, obtained by restriction of scalars along augmentation. -/
def trivialModule : ModuleCat (completedGroupRing Λ G) :=
  (ModuleCat.restrictScalars (completedGroupRing.augmentation Λ G)).obj (ModuleCat.of Λ Λ)

/-- Unfolding of the trivial completed-group-ring module as restriction of scalars of `Λ`. -/
theorem trivialModule_spec :
    trivialModule Λ G =
      (ModuleCat.restrictScalars (completedGroupRing.augmentation Λ G)).obj
        (ModuleCat.of Λ Λ) :=
  sorry
