/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Cancellation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

/-!
# Cancellation for unramified morphisms

Unramifiedness of a composite descends to its left factor. The G-unramified variant additionally
assumes that the right factor is locally of finite type.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- If `f ≫ g` is unramified, then `f` is unramified. -/
theorem Unramified.of_comp
    (f : X ⟶ Y) (g : Y ⟶ S) [Unramified (f ≫ g)] :
    Unramified f :=
  { toFormallyUnramified := FormallyUnramified.of_comp f g
    toLocallyOfFiniteType := locallyOfFiniteType_of_comp f g }

/-- If `f ≫ g` is G-unramified and `g` is locally of finite type, then `f` is G-unramified. -/
theorem GUnramified.of_comp
    (f : X ⟶ Y) (g : Y ⟶ S) [GUnramified (f ≫ g)] [LocallyOfFiniteType g] :
    GUnramified f :=
  { toFormallyUnramified := FormallyUnramified.of_comp f g
    toLocallyOfFinitePresentation := LocallyOfFinitePresentation.of_comp f g }

end AlgebraicGeometry
