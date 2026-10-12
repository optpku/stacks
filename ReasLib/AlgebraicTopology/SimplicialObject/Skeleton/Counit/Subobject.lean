/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Counit
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The subobject represented by a monomorphic skeleton counit

This file isolates the category-generic comparison between a chosen simplicial skeleton and the
subobject represented by its counit. The only substantive input is that the counit is monomorphic;
no additive or abelian structure is needed.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Skeleton.counit

variable {A : Type u} [Category.{v} A]

/-- The canonical isomorphism from a simplicial skeleton to the object underlying the subobject
represented by its monomorphic counit. -/
@[stacks 018U "skeleton as the subobject represented by a monomorphic counit"]
noncomputable def subobjectIso (n : ℕ)
    [SimplicialObject.Truncated.HasSkeletons A n]
    (U : SimplicialObject A) [Mono ((skAdj n).counit.app U)] :
    (sk n).obj U ≅
      (Subobject.mk ((skAdj n).counit.app U) : SimplicialObject A) :=
  (Subobject.underlyingIso ((skAdj n).counit.app U)).symm

namespace subobjectIso

/-- The forward counit-subobject comparison followed by the subobject arrow is the counit. -/
@[reassoc, stacks 018U "counit-subobject comparison over the ambient simplicial object"]
theorem hom_arrow (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    (U : SimplicialObject A) [Mono ((skAdj n).counit.app U)] :
    (subobjectIso n U).hom ≫
        (Subobject.mk ((skAdj n).counit.app U)).arrow =
      (skAdj n).counit.app U := sorry

/-- The inverse counit-subobject comparison followed by the counit is the subobject arrow. -/
@[reassoc, stacks 018U "inverse counit-subobject comparison over the ambient object"]
theorem inv_counit (n : ℕ) [SimplicialObject.Truncated.HasSkeletons A n]
    (U : SimplicialObject A) [Mono ((skAdj n).counit.app U)] :
    (subobjectIso n U).inv ≫ (skAdj n).counit.app U =
      (Subobject.mk ((skAdj n).counit.app U)).arrow := sorry

end subobjectIso

end CategoryTheory.SimplicialObject.Skeleton.counit
