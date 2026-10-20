/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSmooth
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth

/-- For locally finite type morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of locally
Noetherian formal algebraic spaces over a scheme, if `f` is rig-smooth and
rig-surjective and `f ≫ g` is rig-smooth, then `g` is rig-smooth. -/
theorem of_comp_rigSurjective {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [RigSmooth f] [RigSurjective f] [RigSmooth (f ≫ g)] :
    RigSmooth g :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigEtale

/-- For locally finite type morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of locally
Noetherian formal algebraic spaces over a scheme, if `f` is rig-étale and
rig-surjective and `f ≫ g` is rig-étale, then `g` is rig-étale. -/
theorem of_comp_rigSurjective {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [RigEtale f] [RigSurjective f] [RigEtale (f ≫ g)] :
    RigEtale g :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigEtale
