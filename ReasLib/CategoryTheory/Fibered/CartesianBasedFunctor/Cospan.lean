module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Cospan.Basic.Core
import Mathlib.Tactic.CrossRefAttribute

/-!
# Heterogeneous cartesian transformations of cospans

`CartesianCospanTransform` is the cartesian analogue of `BasedCospanTransform`: its three
components are bundled cartesian functors, while the two comparison isomorphisms retain the
explicit pseudonaturality data.  This avoids passing the same cartesian-preservation proofs
separately to every pseudo-pullback consumer.
-/

@[expose] public section

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂
universe uX₃ vX₃ uY₃ vY₃ uS₃ vS₃

namespace CategoryTheory

open BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}
variable {X₃ : BasedCategory.{vX₃, uX₃} C}
variable {Y₃ : BasedCategory.{vY₃, uY₃} C}
variable {S₃ : BasedCategory.{vS₃, uS₃} C}

/-- A universe-polymorphic transformation between cospans of cartesian functors over a common
base. The three component functors are cartesian by construction. -/
@[stacks 04Y1 "cartesian cospan transformation"]
structure CartesianCospanTransform
    (F₁ : CartesianBasedFunctor X₁.p S₁.p)
    (G₁ : CartesianBasedFunctor Y₁.p S₁.p)
    (F₂ : CartesianBasedFunctor X₂.p S₂.p)
    (G₂ : CartesianBasedFunctor Y₂.p S₂.p) where
  /-- The cartesian functor on the left endpoint. -/
  left : CartesianBasedFunctor X₁.p X₂.p
  /-- The cartesian functor on the right endpoint. -/
  right : CartesianBasedFunctor Y₁.p Y₂.p
  /-- The cartesian functor on the common target. -/
  base : CartesianBasedFunctor S₁.p S₂.p
  /-- The comparison along the left cospan leg in the cartesian Hom-category. -/
  leftIso : left.comp F₂ ≅ F₁.comp base
  /-- The comparison along the right cospan leg in the cartesian Hom-category. -/
  rightIso : right.comp G₂ ≅ G₁.comp base

namespace CartesianCospanTransform

variable {F₁ : CartesianBasedFunctor X₁.p S₁.p}
variable {G₁ : CartesianBasedFunctor Y₁.p S₁.p}
variable {F₂ : CartesianBasedFunctor X₂.p S₂.p}
variable {G₂ : CartesianBasedFunctor Y₂.p S₂.p}
variable {F₃ : CartesianBasedFunctor X₃.p S₃.p}
variable {G₃ : CartesianBasedFunctor Y₃.p S₃.p}

/-- The identity transformation of a cospan of heterogeneous cartesian functors. -/
@[stacks 04Y1 "identity cartesian cospan transformation"]
def id (F : CartesianBasedFunctor X₁.p S₁.p)
    (G : CartesianBasedFunctor Y₁.p S₁.p) :
    CartesianCospanTransform F G F G where
  left := CartesianBasedFunctor.id X₁.p
  right := CartesianBasedFunctor.id Y₁.p
  base := CartesianBasedFunctor.id S₁.p
  leftIso := ObjectProperty.isoMk _ (BasedNatIso.id F.toBasedFunctor)
  rightIso := ObjectProperty.isoMk _ (BasedNatIso.id G.toBasedFunctor)

/-- Vertical composition of heterogeneous cartesian cospan transformations. -/
@[stacks 04Y1 "composition of cartesian cospan transformations"]
def comp
    (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂)
    (φ : CartesianCospanTransform F₂ G₂ F₃ G₃) :
    CartesianCospanTransform F₁ G₁ F₃ G₃ where
  left := ψ.left.comp φ.left
  right := ψ.right.comp φ.right
  base := ψ.base.comp φ.base
  leftIso := ObjectProperty.isoMk _
    (BasedNatIso.whiskerLeft ψ.left.toBasedFunctor
        (CartesianBasedFunctor.toBasedIso φ.leftIso) ≪≫
      BasedNatIso.whiskerRight
        (CartesianBasedFunctor.toBasedIso ψ.leftIso) φ.base.toBasedFunctor)
  rightIso := ObjectProperty.isoMk _
    (BasedNatIso.whiskerLeft ψ.right.toBasedFunctor
        (CartesianBasedFunctor.toBasedIso φ.rightIso) ≪≫
      BasedNatIso.whiskerRight
        (CartesianBasedFunctor.toBasedIso ψ.rightIso) φ.base.toBasedFunctor)

/-- Forget cartesian preservation from the three components of a cartesian cospan
transformation. -/
@[stacks 04Y1 "underlying based cospan transformation"]
def toBased (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂) :
    BasedCospanTransform F₁.toBasedFunctor G₁.toBasedFunctor
      F₂.toBasedFunctor G₂.toBasedFunctor :=
  BasedCospanTransform.mk ψ.left.toBasedFunctor ψ.right.toBasedFunctor ψ.base.toBasedFunctor
    (CartesianBasedFunctor.toBasedIso ψ.leftIso)
    (CartesianBasedFunctor.toBasedIso ψ.rightIso)

/-- The left component of the underlying based cospan transformation is the underlying based
functor of the cartesian left component. -/
@[simp, stacks 04Y1 "left component readout of a cartesian cospan transformation"]
theorem toBased.left (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂) :
    ψ.toBased.left = ψ.left.toBasedFunctor := sorry

/-- The right component of the underlying based cospan transformation is the underlying based
functor of the cartesian right component. -/
@[simp, stacks 04Y1 "right component readout of a cartesian cospan transformation"]
theorem toBased.right (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂) :
    ψ.toBased.right = ψ.right.toBasedFunctor := sorry

/-- The common-target component of the underlying based cospan transformation is the underlying
based functor of the cartesian common-target component. -/
@[simp, stacks 04Y1 "base component readout of a cartesian cospan transformation"]
theorem toBased.base (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂) :
    ψ.toBased.base = ψ.base.toBasedFunctor := sorry

/-- The left comparison of the underlying based transformation is the canonical forgotten
cartesian comparison. -/
@[simp, stacks 04Y1 "left comparison readout of a cartesian cospan transformation"]
theorem toBased.leftIso (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂) :
    ψ.toBased.leftIso = CartesianBasedFunctor.toBasedIso ψ.leftIso := sorry

/-- The right comparison of the underlying based transformation is the canonical forgotten
cartesian comparison. -/
@[simp, stacks 04Y1 "right comparison readout of a cartesian cospan transformation"]
theorem toBased.rightIso (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂) :
    ψ.toBased.rightIso = CartesianBasedFunctor.toBasedIso ψ.rightIso := sorry

/-- Forgetting the identity cartesian cospan transformation gives the identity based cospan
transformation. -/
@[simp, stacks 04Y1 "identity underlying based cospan transformation"]
theorem id.toBased
    (F : CartesianBasedFunctor X₁.p S₁.p)
    (G : CartesianBasedFunctor Y₁.p S₁.p) :
    (id F G).toBased =
      BasedCospanTransform.id F.toBasedFunctor G.toBasedFunctor := sorry

/-- Forgetting a composite cartesian cospan transformation gives the composite of the
underlying based transformations. -/
@[simp, stacks 04Y1 "composite underlying based cospan transformation"]
theorem comp.toBased
    (ψ : CartesianCospanTransform F₁ G₁ F₂ G₂)
    (φ : CartesianCospanTransform F₂ G₂ F₃ G₃) :
    (comp ψ φ).toBased = BasedCospanTransform.comp ψ.toBased φ.toBased := sorry

/-- Bundle a based cospan transformation whose three components preserve strongly cartesian
arrows. -/
@[stacks 04Y1 "cartesian cospan transformation from based data"]
def ofBased
    (ψ : BasedCospanTransform F₁.toBasedFunctor G₁.toBasedFunctor
      F₂.toBasedFunctor G₂.toBasedFunctor)
    (hleft : ψ.left.PreservesStronglyCartesian)
    (hright : ψ.right.PreservesStronglyCartesian)
    (hbase : ψ.base.PreservesStronglyCartesian) :
    CartesianCospanTransform F₁ G₁ F₂ G₂ where
  left := CartesianBasedFunctor.ofBasedFunctor ψ.left hleft
  right := CartesianBasedFunctor.ofBasedFunctor ψ.right hright
  base := CartesianBasedFunctor.ofBasedFunctor ψ.base hbase
  leftIso := ObjectProperty.isoMk _ ψ.leftIso
  rightIso := ObjectProperty.isoMk _ ψ.rightIso

/-- The based transformation underlying `ofBased` is the supplied transformation. -/
@[simp, stacks 04Y1 "underlying transformation of the cartesian cospan lift"]
theorem ofBased.toBased
    (ψ : BasedCospanTransform F₁.toBasedFunctor G₁.toBasedFunctor
      F₂.toBasedFunctor G₂.toBasedFunctor)
    (hleft : ψ.left.PreservesStronglyCartesian)
    (hright : ψ.right.PreservesStronglyCartesian)
    (hbase : ψ.base.PreservesStronglyCartesian) :
    (ofBased ψ hleft hright hbase).toBased = ψ := sorry

end CartesianCospanTransform

end CategoryTheory

/- Axiom audit: `toBased` only forgets proof-valued cartesian fields, while `ofBased` stores the
three supplied preservation witnesses without choosing any functor or comparison datum. -/
