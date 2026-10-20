module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import ReasLib.Topology.Algebra.OpenNormalSubgroup

/-!
# Completed group rings

Compatible families over open normal quotients form a subring of the product
of group rings. Coefficients may belong to any ring.
-/

@[expose] public section

open CategoryTheory
open scoped MonoidAlgebra

noncomputable section

universe u v

variable (Λ : Type u) [Ring Λ]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Transition between the group rings of two open normal quotients. -/
def CompletedGroupRing.transition {N N' : OpenNormalSubgroup G} (h : N ≤ N') :
    MonoidAlgebra Λ (G ⧸ N.toSubgroup) →+* MonoidAlgebra Λ (G ⧸ N'.toSubgroup) :=
  MonoidAlgebra.mapDomainRingHom Λ
    (QuotientGroup.map N.toSubgroup N'.toSubgroup (MonoidHom.id G) h)

/-- Compatibility of a family with the quotient transition maps. -/
def CompletedGroupRing.IsCompatible
    (f : ∀ N : OpenNormalSubgroup G, MonoidAlgebra Λ (G ⧸ N.toSubgroup)) : Prop :=
  ∀ ⦃N N' : OpenNormalSubgroup G⦄ (h : N ≤ N'),
    CompletedGroupRing.transition Λ G h (f N) = f N'

/-- Compatible families form a subring with the inherited pointwise operations. -/
def CompletedGroupRing.compatibleSubring :
    Subring (∀ N : OpenNormalSubgroup G, MonoidAlgebra Λ (G ⧸ N.toSubgroup)) where
  carrier := {f | CompletedGroupRing.IsCompatible Λ G f}
  zero_mem' := by intro N N' h; exact map_zero _
  one_mem' := by intro N N' h; exact map_one _
  add_mem' := by
    intro a b ha hb N N' h
    change CompletedGroupRing.transition Λ G h (a N + b N) = a N' + b N'
    rw [map_add, ha h, hb h]
  mul_mem' := by
    intro a b ha hb N N' h
    change CompletedGroupRing.transition Λ G h (a N * b N) = a N' * b N'
    rw [map_mul, ha h, hb h]
  neg_mem' := by
    intro a ha N N' h
    change CompletedGroupRing.transition Λ G h (-a N) = -a N'
    rw [map_neg, ha h]

/-- The completed group ring as the compatible subring of all quotient group rings. -/
abbrev completedGroupRing := CompletedGroupRing.compatibleSubring Λ G

namespace completedGroupRing

/-- A compatible family is determined by its quotient coordinates. -/
@[ext]
theorem ext {a b : completedGroupRing Λ G} (h : ∀ N, a.val N = b.val N) : a = b :=
  Subtype.ext (funext h)

/-- Projection to the group ring of an open normal quotient. -/
def π (N : OpenNormalSubgroup G) :
    completedGroupRing Λ G →+* MonoidAlgebra Λ (G ⧸ N.toSubgroup) where
  toFun f := f.val N
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Scalar inclusion at every quotient, valid for noncommutative coefficients. -/
def ofScalar : Λ →+* completedGroupRing Λ G where
  toFun r := ⟨fun _ ↦ (MonoidAlgebra.singleOneRingHom : Λ →+* _) r, by sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The compatible Dirac family of a group element. -/
def dirac (g : G) : completedGroupRing Λ G :=
  ⟨fun N ↦ MonoidAlgebra.single (QuotientGroup.mk g : G ⧸ N.toSubgroup) 1, by sorry⟩

/-- Augmentation evaluates the coefficient of the identity in the trivial quotient. -/
def augmentation : completedGroupRing Λ G →+* Λ where
  toFun f := (π Λ G (⊤ : OpenNormalSubgroup G) f).coeff 1
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Scalars have their supplied value in every quotient group ring. -/
@[simp]
theorem π_ofScalar (N : OpenNormalSubgroup G) (a : Λ) :
    π Λ G N (ofScalar Λ G a) = MonoidAlgebra.singleOneRingHom a := rfl

/-- Dirac families project to the corresponding quotient group element. -/
@[simp]
theorem π_dirac (N : OpenNormalSubgroup G) (g : G) :
    π Λ G N (dirac Λ G g) = MonoidAlgebra.single (QuotientGroup.mk g) 1 := rfl

/-- The augmentation splits scalar inclusion. -/
@[simp]
theorem augmentation_ofScalar (a : Λ) : augmentation Λ G (ofScalar Λ G a) = a := sorry

end completedGroupRing

/-- The coefficient ring as a trivial module through augmentation. -/
def trivialModule : ModuleCat (completedGroupRing Λ G) :=
  (ModuleCat.restrictScalars (completedGroupRing.augmentation Λ G)).obj (ModuleCat.of Λ Λ)

/-- The trivial completed module is restriction of the regular coefficient module. -/
theorem trivialModule_spec :
    trivialModule Λ G =
      (ModuleCat.restrictScalars (completedGroupRing.augmentation Λ G)).obj
        (ModuleCat.of Λ Λ) := rfl
