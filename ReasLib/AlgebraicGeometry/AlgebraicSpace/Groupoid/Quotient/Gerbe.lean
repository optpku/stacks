/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Trivial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Functoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.StructureMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction.Comparison
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.GerbeMorphism

/-!
# Gerbe morphisms of quotient stacks

The morphism of quotient stacks induced by a groupoid morphism is a gerbe when
the object map and the comparison to the restricted arrow space are locally
surjective for the fppf topology.
The quotient stack of the trivial action on the base is a gerbe over that base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

namespace Hom

/-- A morphism of groupoids in algebraic spaces induces a gerbe morphism of
fppf quotient stacks if its object map and its canonical comparison to the
target arrow space restricted along the object map are locally surjective
for the fppf topology. -/
@[stacks 06PE]
theorem quotientStackMap_isGerbeMorphism {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H)
    (h_obj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f.obj.left)
    (h_arrow : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      f.restrictionArrow.left) :
    CartesianBasedFunctor.IsGerbeMorphism (Scheme.fppfTopology.over S) f.quotientStackMap :=
  sorry

end Hom

/-- For a group algebraic space `G` over `B`, the canonical morphism from the
quotient stack of the trivial action on `B` to the stack of points of `B` is a
gerbe morphism for the fppf topology. -/
theorem toBase_trivialAction_isGerbeMorphism {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    CartesianBasedFunctor.IsGerbeMorphism (Scheme.fppfTopology.over S)
      (toBase (ofAction G (trivialAction G))) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
