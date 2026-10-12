/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Counit.Subobject
public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Generated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Generic comparisons with bounded-degree generation

Given a monomorphic skeleton counit and its equality with bounded-degree generation, this file
constructs the corresponding objectwise and natural isomorphisms. Category-specific proofs of the
subobject equality and their canonical comparison facades live in downstream specialization
leaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Skeleton

section Comparison

variable {A : Type u} [Category.{v} A]
variable [HasPullbacks A] [HasImages A] [HasBinaryCoproducts A]

namespace generated.comparison

/-- The skeleton-to-generated-subobject isomorphism determined by a subobject equality. This is
the category-generic constructor underlying `generated.subobjectIso`. -/
@[stacks 018U "generic skeleton-generated subobject comparison"]
noncomputable def subobjectIso (n : ℕ)
    [SimplicialObject.Truncated.HasSkeletons A n]
    (U : SimplicialObject A) [Mono ((skAdj n).counit.app U)]
    (h : Subobject.mk ((skAdj n).counit.app U) = U.generated n) :
    (sk n).obj U ≅ (U.generated n : SimplicialObject A) :=
  counit.subobjectIso n U ≪≫ Subobject.isoOfEq _ _ h

namespace subobjectIso

/-- A generic generated-subobject comparison lies over the skeleton counit. -/
@[reassoc, stacks 018U "generic generated-subobject comparison over the ambient object"]
theorem hom_arrow (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    (U : SimplicialObject A) [Mono ((skAdj n).counit.app U)]
    (h : Subobject.mk ((skAdj n).counit.app U) = U.generated n) :
    (generated.comparison.subobjectIso n U h).hom ≫ (U.generated n).arrow =
      (skAdj n).counit.app U := sorry

/-- The inverse generic comparison followed by the counit is the generated-subobject arrow. -/
@[reassoc, stacks 018U "inverse generic generated-subobject comparison"]
theorem inv_counit (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    (U : SimplicialObject A) [Mono ((skAdj n).counit.app U)]
    (h : Subobject.mk ((skAdj n).counit.app U) = U.generated n) :
    (generated.comparison.subobjectIso n U h).inv ≫ (skAdj n).counit.app U =
      (U.generated n).arrow := sorry

end subobjectIso

/-- The objectwise skeleton-generated comparison determined by a subobject equality. -/
@[stacks 018U "generic objectwise skeleton-generated comparison"]
noncomputable def isoApp (n : ℕ)
    [SimplicialObject.Truncated.HasSkeletons A n]
    (U : SimplicialObject A) [Mono ((skAdj n).counit.app U)]
    (h : Subobject.mk ((skAdj n).counit.app U) = U.generated n) :
    (sk n).obj U ≅ SimplicialObject.generated.obj U n :=
  subobjectIso n U h ≪≫
    Subobject.underlyingIso (SimplicialObject.generated.inclusion U n)

namespace isoApp

/-- A family of generic objectwise comparisons is natural when induced by subobject equalities. -/
@[stacks 018U "naturality of generic objectwise skeleton-generated comparisons"]
theorem naturality (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    [∀ U : SimplicialObject A, Mono ((skAdj n).counit.app U)]
    (h : ∀ U : SimplicialObject A,
      Subobject.mk ((skAdj n).counit.app U) = U.generated n)
    {U V : SimplicialObject A} (f : U ⟶ V) :
    (sk n).map f ≫ (generated.comparison.isoApp n V (h V)).hom =
      (generated.comparison.isoApp n U (h U)).hom ≫
        (SimplicialObject.generated.functor n).map f := sorry

/-- A generic objectwise comparison followed by the generated inclusion is the counit. -/
@[reassoc, stacks 018U "generic objectwise comparison over the ambient object"]
theorem hom_inclusion (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    (U : SimplicialObject A) [Mono ((skAdj n).counit.app U)]
    (h : Subobject.mk ((skAdj n).counit.app U) = U.generated n) :
    (generated.comparison.isoApp n U h).hom ≫
        SimplicialObject.generated.inclusion U n =
      (skAdj n).counit.app U := sorry

/-- The inverse generic objectwise comparison followed by the counit is the generated
inclusion. -/
@[reassoc, stacks 018U "inverse generic objectwise skeleton-generated comparison"]
theorem inv_counit (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    (U : SimplicialObject A) [Mono ((skAdj n).counit.app U)]
    (h : Subobject.mk ((skAdj n).counit.app U) = U.generated n) :
    (generated.comparison.isoApp n U h).inv ≫ (skAdj n).counit.app U =
      SimplicialObject.generated.inclusion U n := sorry

end isoApp

/-- The natural skeleton-generated isomorphism determined by a family of subobject equalities. -/
@[stacks 018U "generic natural skeleton-generated comparison"]
noncomputable def iso (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    [∀ U : SimplicialObject A, Mono ((skAdj n).counit.app U)]
    (h : ∀ U : SimplicialObject A,
      Subobject.mk ((skAdj n).counit.app U) = U.generated n) :
    sk (C := A) n ≅ SimplicialObject.generated.functor (A := A) n :=
  NatIso.ofComponents (fun U ↦ isoApp n U (h U))
    (fun f ↦ isoApp.naturality n h f)

/-- The component of a generic natural skeleton-generated comparison is its objectwise
comparison. -/
@[simp, stacks 018U "component of a generic skeleton-generated comparison"]
theorem iso_app (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    [∀ U : SimplicialObject A, Mono ((skAdj n).counit.app U)]
    (h : ∀ U : SimplicialObject A,
      Subobject.mk ((skAdj n).counit.app U) = U.generated n)
    (U : SimplicialObject A) :
    (generated.comparison.iso n h).app U =
      generated.comparison.isoApp n U (h U) := sorry

namespace iso

/-- The forward component of a generic natural comparison is its objectwise comparison. -/
@[simp, stacks 018U "forward component of a generic skeleton-generated comparison"]
theorem hom_app (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    [∀ U : SimplicialObject A, Mono ((skAdj n).counit.app U)]
    (h : ∀ U : SimplicialObject A,
      Subobject.mk ((skAdj n).counit.app U) = U.generated n)
    (U : SimplicialObject A) :
    (generated.comparison.iso n h).hom.app U =
      (generated.comparison.isoApp n U (h U)).hom := sorry

/-- The inverse component of a generic natural comparison is its inverse objectwise comparison. -/
@[simp, stacks 018U "inverse component of a generic skeleton-generated comparison"]
theorem inv_app (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    [∀ U : SimplicialObject A, Mono ((skAdj n).counit.app U)]
    (h : ∀ U : SimplicialObject A,
      Subobject.mk ((skAdj n).counit.app U) = U.generated n)
    (U : SimplicialObject A) :
    (generated.comparison.iso n h).inv.app U =
      (generated.comparison.isoApp n U (h U)).inv := sorry

/-- A generic natural comparison followed by the generated inclusion is the counit. -/
@[reassoc, stacks 018U "generic natural comparison over the identity functor"]
theorem hom_ι (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    [∀ U : SimplicialObject A, Mono ((skAdj n).counit.app U)]
    (h : ∀ U : SimplicialObject A,
      Subobject.mk ((skAdj n).counit.app U) = U.generated n) :
    (generated.comparison.iso n h).hom ≫
        SimplicialObject.generated.ι (A := A) n =
      (skAdj (C := A) n).counit := sorry

/-- The inverse generic natural comparison followed by the counit is the generated inclusion. -/
@[reassoc, stacks 018U "inverse generic natural skeleton-generated comparison"]
theorem inv_counit (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    [∀ U : SimplicialObject A, Mono ((skAdj n).counit.app U)]
    (h : ∀ U : SimplicialObject A,
      Subobject.mk ((skAdj n).counit.app U) = U.generated n) :
    (generated.comparison.iso n h).inv ≫ (skAdj (C := A) n).counit =
      SimplicialObject.generated.ι (A := A) n := sorry

end iso

end generated.comparison

end Comparison

end CategoryTheory.SimplicialObject.Skeleton
