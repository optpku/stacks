/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.McQuillan
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.EtaleDescent
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Colimits

/-!
# Pullbacks of formal algebraic spaces

On a chosen big fppf site, formal algebraic spaces are closed under pullbacks
over a sheaf whose diagonal is representable by algebraic spaces. Affine and
McQuillan formal algebraic spaces are closed under pullbacks over a separated
formal algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

namespace IsAffineFormalAlgebraicSpace

/-- Over a separated formal algebraic space, the pullback of two
affine formal algebraic spaces is affine. -/
instance instPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    [IsSeparatedFormalAlgebraicSpace Z] :
    IsAffineFormalAlgebraicSpace (pullback f g) :=
  sorry

/-- The fibre product object of an `IsPullback` square of morphisms into a
separated formal algebraic space is an affine formal algebraic space when the
two sources are. -/
theorem of_isPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Y' Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f)
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    [IsSeparatedFormalAlgebraicSpace Z] :
    IsAffineFormalAlgebraicSpace Y' :=
  sorry

end IsAffineFormalAlgebraicSpace

namespace IsMcQuillan

/-- Over a separated formal algebraic space, the pullback of two
McQuillan affine formal algebraic spaces is McQuillan. -/
instance instPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsMcQuillan X] [IsMcQuillan Y]
    [IsSeparatedFormalAlgebraicSpace Z] :
    IsMcQuillan (pullback f g) :=
  sorry

/-- The fibre product object of an `IsPullback` square of morphisms into a
separated formal algebraic space is McQuillan when the two sources are. -/
theorem of_isPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Y' Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {f : X ⟶ Z} {g : Y ⟶ Z} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f)
    [IsMcQuillan X] [IsMcQuillan Y]
    [IsSeparatedFormalAlgebraicSpace Z] :
    IsMcQuillan Y' :=
  sorry

end IsMcQuillan

namespace IsFormalAlgebraicSpace

/-- The pullback of two formal algebraic spaces over a sheaf whose diagonal is
representable by algebraic spaces is a formal algebraic space. -/
theorem ofPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (h_diag : representableByAlgebraicSpaces (diag Z)) :
    IsFormalAlgebraicSpace (pullback f g) := sorry

/-- The apex of an `IsPullback` square of morphisms of sheaves into a sheaf
whose diagonal is representable by algebraic spaces is a formal algebraic
space when the two sources are. -/
theorem of_isPullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z P : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    {f : X ⟶ Z} {g : Y ⟶ Z} {fst : P ⟶ X} {snd : P ⟶ Y}
    (sq : IsPullback fst snd f g)
    (h_diag : representableByAlgebraicSpaces (diag Z)) :
    IsFormalAlgebraicSpace P := sorry

end IsFormalAlgebraicSpace

end AlgebraicGeometry
