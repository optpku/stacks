/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Coherence and full support under finite surjective morphisms

The structure module of the inverse image of a closed subspace under a finite
surjective morphism with locally Noetherian target has coherent pushforward
with full support on the closed subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a finite surjective morphism of algebraic spaces with locally Noetherian
target and a closed immersion into that target, the pushforward of the structure
module of the inverse image to the closed subspace is coherent. -/
@[stacks 0GF7]
instance pushforward_inverseImageTo_unit_isCoherent
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] :
    ((pushforward (inverseImageTo f i)).obj
        (SheafOfModules.unit (structureSheaf (inverseImage f i)))).IsCoherent :=
  sorry

/-- For a finite surjective morphism of algebraic spaces with locally Noetherian
target and a closed immersion into that target, the pushforward of the structure
module of the inverse image has support equal to the whole closed subspace. -/
@[stacks 0GF7]
theorem moduleSupport_pushforward_inverseImageTo_unit_eq_univ
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] :
    moduleSupport
        ((pushforward (inverseImageTo f i)).obj
          (SheafOfModules.unit (structureSheaf (inverseImage f i)))) =
      (Set.univ : Set (Points Z)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
