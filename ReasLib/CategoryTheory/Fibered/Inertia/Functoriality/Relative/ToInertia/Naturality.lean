/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.ToInertia.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of relative-to-absolute inertia on pseudo-comma arrows

This leaf records compatibility of the canonical comparison with pseudo-comma `2`-cells,
together with its objectwise form.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia
namespace pseudoComma

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}

noncomputable section

namespace toInertiaIso

/-- The relative-to-absolute comparison is compatible with a pseudo-comma
`2`-morphism: the induced relative-inertia cell and the absolute-inertia cell
of its left endpoint commute through the two comparison isomorphisms. -/
@[stacks 04Z5 "relative-to-absolute inertia comparison naturality"]
theorem naturality
    {f g : S ⟶ T} (η : f ⟶ g) :
    BasedCategory.whiskerRight (pseudoComma.map₂ η) (RelativeInertia.toInertia T.hom) ≫
        (toInertiaIso g).hom =
      (toInertiaIso f).hom ≫
        BasedCategory.whiskerLeft (RelativeInertia.toInertia S.hom)
          (Inertia.map₂ (Bicategory.PseudoComma.left₂ η)) := sorry

/-- Objectwise form of `toInertiaIso.naturality`, avoiding expansion of either whiskered
based `2`-morphism. -/
@[stacks 04Z5 "relative-to-absolute inertia comparison objectwise naturality"]
theorem naturality.app
    {f g : S ⟶ T} (η : f ⟶ g) (A : (relativeInertia S.hom).obj) :
    (RelativeInertia.toInertia T.hom).toFunctor.map
        ((pseudoComma.map₂ η).toNatTrans.app A) ≫
        (toInertiaIso g).hom.toNatTrans.app A =
      (toInertiaIso f).hom.toNatTrans.app A ≫
        (Inertia.map₂ (Bicategory.PseudoComma.left₂ η)).toNatTrans.app
          ((RelativeInertia.toInertia S.hom).toFunctor.obj A) := sorry

/-- The inverse pseudo-comma comparison satisfies the reverse naturality equation. -/
@[reassoc, stacks 04Z5 "relative-to-absolute inertia inverse comparison naturality"]
theorem invNaturality
    {f g : S ⟶ T} (η : f ⟶ g) :
    (toInertiaIso f).inv ≫
        BasedCategory.whiskerRight (pseudoComma.map₂ η) (RelativeInertia.toInertia T.hom) =
      BasedCategory.whiskerLeft (RelativeInertia.toInertia S.hom)
          (Inertia.map₂ (Bicategory.PseudoComma.left₂ η)) ≫
        (toInertiaIso g).inv := sorry

/-- Objectwise form of `toInertiaIso.invNaturality`. -/
@[reassoc, stacks 04Z5 "relative-to-absolute inertia inverse objectwise naturality"]
theorem invNaturality.app
    {f g : S ⟶ T} (η : f ⟶ g) (A : (relativeInertia S.hom).obj) :
    (toInertiaIso f).inv.toNatTrans.app A ≫
        (RelativeInertia.toInertia T.hom).toFunctor.map
          ((pseudoComma.map₂ η).toNatTrans.app A) =
      (Inertia.map₂ (Bicategory.PseudoComma.left₂ η)).toNatTrans.app
          ((RelativeInertia.toInertia S.hom).toFunctor.obj A) ≫
        (toInertiaIso g).inv.toNatTrans.app A := sorry

end toInertiaIso

end

end pseudoComma
end RelativeInertia
end BasedCategory
end CategoryTheory
