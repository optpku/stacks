/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.IsoComma
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Equivalences of quotient stacks

The canonical morphism of fppf quotient stacks induced by a morphism of groupoids
is an equivalence exactly when the source is a restriction and the iso-comma
structure map is locally surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

/-- The canonical morphism of fppf quotient stacks induced by a morphism of
groupoids in algebraic spaces is an equivalence over the base if and only if the
source is the restriction of the target along the object map and the map
`U ×_{f, U', t'} R' ⟶ U'` given by the source of the arrow factor is locally
surjective for the fppf topology. -/
theorem quotientStackMap_isEquivalence_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    f.quotientStackMap.toBasedFunctor.IsEquivalence ↔
      IsRestriction f ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (isoCommaToTargetObject f).left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
