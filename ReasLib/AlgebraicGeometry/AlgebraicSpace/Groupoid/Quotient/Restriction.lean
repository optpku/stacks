/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Functoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction.Comparison

/-!
# Full faithfulness of morphisms of quotient stacks

The canonical morphism of fppf quotient stacks induced by a morphism of groupoids
is fully faithful exactly when its arrow space is obtained by restriction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

/-- The canonical morphism of fppf quotient stacks induced by a morphism of
 groupoids in algebraic spaces is fully faithful if and only if the source arrow
 space is the restriction of the target arrow space along the object map. -/
theorem quotientStackMap_fullyFaithful_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    Nonempty f.quotientStackMap.toFunctor.FullyFaithful ↔ IsRestriction f := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
