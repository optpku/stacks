/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A local complete-intersection morphism cancels after smooth postcomposition:
if `g` is smooth (the étale-local lift of smoothness of scheme morphisms) and
`f ≫ g` is a local complete intersection, then so is `f`. -/
theorem isLocalCompleteIntersection_of_smooth_of_comp
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : etaleLocal @AlgebraicGeometry.Smooth g)
    (hfg : IsLocalCompleteIntersection (f ≫ g)) :
    IsLocalCompleteIntersection f := sorry

/-- Local complete-intersection morphisms have the postcomposition cancellation
property with respect to smooth morphisms. -/
instance instLciHasOfPostcompPropertySmooth {S : Scheme.{u}} :
    MorphismProperty.HasOfPostcompProperty
      (@IsLocalCompleteIntersection S)
      (etaleLocal (S := S) @AlgebraicGeometry.Smooth) := sorry

namespace IsKoszulRegularImmersion

/-- An immersion `i : U ⟶ P` over `Y` is Koszul-regular if `U` is étale over
an algebraic space `X` that is a local complete intersection over `Y`, and
`P` is smooth over `Y`. -/
theorem of_localCompleteIntersection_over_smooth {S : Scheme.{u}}
    {X Y P U : AlgebraicSpace S} (f : X ⟶ Y) (p : P ⟶ Y) (u : U ⟶ X) (i : U ⟶ P)
    [IsLocalCompleteIntersection f] [Smooth p] [Etale u] [IsImmersion i]
    (h_over : i ≫ p = u ≫ f) : IsKoszulRegularImmersion i :=
  sorry

end IsKoszulRegularImmersion

end AlgebraicGeometry.AlgebraicSpace
