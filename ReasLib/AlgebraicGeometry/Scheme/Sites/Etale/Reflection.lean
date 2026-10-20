/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyC
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.CategoryTheory.Sites.DenseSubsite.Reflection

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

/-- Property (C) gives monomorphism reflection for the small étale direct
image of a scheme morphism. -/
theorem smallMorphism_pushforward_reflectsMonomorphisms_of_hasPropertyC
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (Type (u + 1))]
    (hC : hasPropertyC f) :
    (smallMorphism f).pushforward.ReflectsMonomorphisms := sorry

/-- Property (C) gives epimorphism reflection for the small étale direct image
of a scheme morphism. -/
theorem smallMorphism_pushforward_reflectsEpimorphisms_of_hasPropertyC
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (Type (u + 1))]
    [HasSheafify Y.smallEtaleTopology (Type (u + 1))]
    (hC : hasPropertyC f) :
    (smallMorphism f).pushforward.ReflectsEpimorphisms := sorry

end AlgebraicGeometry.Scheme.Etale.SmallToBig
