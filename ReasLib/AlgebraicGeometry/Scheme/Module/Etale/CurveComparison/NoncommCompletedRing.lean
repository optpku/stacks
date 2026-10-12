/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.Proposition_64_29_3_CompletedGroupRingAlgebra

@[expose] public section
open CategoryTheory
open scoped MonoidAlgebra
noncomputable section
universe u v

namespace NoncommCompletedRing
section General
variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Finite-quotient group-algebra transition for an arbitrary coefficient ring. -/
def transition {N N' : OpenNormalSubgroup G} (h : N ≤ N') :
    MonoidAlgebra R (G ⧸ N.toSubgroup) →+* MonoidAlgebra R (G ⧸ N'.toSubgroup) :=
  MonoidAlgebra.mapDomainRingHom R
    (QuotientGroup.map N.toSubgroup N'.toSubgroup (MonoidHom.id G) h)

/-- The inverse-limit compatibility equations cut out a genuine subring. -/
def compatible : Subring (∀ N : OpenNormalSubgroup G, MonoidAlgebra R (G ⧸ N.toSubgroup)) where
  carrier := {x | ∀ ⦃N N' : OpenNormalSubgroup G⦄ (h : N ≤ N'), transition R G h (x N) = x N'}
  zero_mem' := by intro N N' h; exact map_zero _
  one_mem' := by intro N N' h; exact map_one _
  add_mem' := by
    intro x y hx hy N N' h
    change transition R G h (x N + y N) = x N' + y N'
    rw [map_add, hx h, hy h]
  mul_mem' := by
    intro x y hx hy N N' h
    change transition R G h (x N * y N) = x N' * y N'
    rw [map_mul, hx h, hy h]
  neg_mem' := by
    intro x hx N N' h
    change transition R G h (-x N) = -x N'
    rw [map_neg, hx h]

/-- Completed group ring as actual compatible families, with no commutativity assumption. -/
abbrev Obj := compatible R G

/-- The specified finite-stage projection. -/
def projection (N : OpenNormalSubgroup G) : Obj R G →+* MonoidAlgebra R (G ⧸ N.toSubgroup) where
  toFun x := x.val N
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Scalar inclusion uses the single-one ring homomorphism, not algebraMap
over a falsely commutative coefficient ring. -/
def ofScalar : R →+* Obj R G where
  toFun r := ⟨fun N ↦ (MonoidAlgebra.singleOneRingHom :
      R →+* MonoidAlgebra R (G ⧸ N.toSubgroup)) r, by sorry⟩
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

/-- Actual Dirac compatible family of a group element. -/
def dirac (g : G) : Obj R G :=
  ⟨fun N ↦ MonoidAlgebra.single (QuotientGroup.mk g : G ⧸ N.toSubgroup) 1, by sorry⟩

/-- Augmentation evaluates the trivial finite-group quotient. -/
def augmentation : Obj R G →+* R where
  toFun x := (projection R G ⊤ x).coeff 1
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

end General

/-- Compatibility with the existing commutative-coefficient owner is identity
on actual compatible families, not a new group/topology transport. -/
def commutativeComparison (R : Type u) [CommRing R]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Obj R G ≃+* completedGroupRing R G where
  toFun x := ⟨x.val, by sorry⟩
  invFun x := ⟨x.val, by sorry⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl

end NoncommCompletedRing
