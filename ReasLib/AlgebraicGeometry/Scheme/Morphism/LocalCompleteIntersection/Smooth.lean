/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Koszul

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Smooth
import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.SourceLocus

/-!
# Local complete intersection morphisms over smooth morphisms

This module gives the postcomposition cancellation property for local complete intersection
morphisms when the second morphism is smooth. It also shows that an immersion from an open
subscheme of the source of a local complete intersection morphism into a smooth ambient scheme
is Koszul-regular.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- Local complete intersection morphisms can be cancelled after postcomposition with a smooth
morphism. -/
instance instIsLocalCompleteIntersectionHasOfPostcompPropertySmooth :
    MorphismProperty.HasOfPostcompProperty
      (@AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection)
      (@AlgebraicGeometry.Smooth : MorphismProperty Scheme) := sorry

/-- In a commutative triangle of scheme morphisms, if the second morphism is smooth and the
composite is a local complete intersection morphism, then the first morphism is a local complete
intersection morphism. -/
theorem isLocalCompleteIntersection_of_smooth_of_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S)
    (hcomm : f ≫ g = h) [Smooth g]
    (hX : LocallyOfType RingHom.IsLocalCompleteIntersection h) :
    LocallyOfType RingHom.IsLocalCompleteIntersection f := by
  exact MorphismProperty.of_postcomp
    (W' := @AlgebraicGeometry.Smooth)
    (@AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection) f g
    (by infer_instance) (hcomm.symm ▸ hX)

end AlgebraicGeometry.LocallyOfType

namespace AlgebraicGeometry.IsKoszulRegularImmersion

/-- An immersion from an open subscheme of the source of a local complete intersection morphism
into a smooth scheme over the same base is Koszul-regular. -/
theorem of_localCompleteIntersection_over_smooth
    {X P S : Scheme.{u}} (f : X ⟶ S) (p : P ⟶ S) (U : X.Opens)
    (i : U.toScheme ⟶ P) [Smooth p] [IsImmersion i]
    (h_lci : LocallyOfType RingHom.IsLocalCompleteIntersection f)
    (h_over : i ≫ p = U.ι ≫ f) :
    IsKoszulRegularImmersion i := sorry

end AlgebraicGeometry.IsKoszulRegularImmersion
