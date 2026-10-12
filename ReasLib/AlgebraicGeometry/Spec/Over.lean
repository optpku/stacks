/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.RingHomProperties
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Over
public import ReasLib.RingTheory.RingHom.Local.Properties

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace RingHom.IsIsoOnLocalRings

/-- The category of `A`-algebras whose structure map identifies local rings. -/
abbrev Under (A : CommRingCat.{u}) :=
  (toMorphismProperty IsIsoOnLocalRings).Under ⊤ A

/-- Structure maps of objects of `RingHom.IsIsoOnLocalRings.Under` identify local rings. -/
theorem under_hom {A : CommRingCat.{u}} (B : Under A) :
    IsIsoOnLocalRings B.hom.hom :=
  sorry

end RingHom.IsIsoOnLocalRings

namespace AlgebraicGeometry.Spec

/-- Spec as a contravariant functor from `A`-algebras to topological spaces over `Spec A`. -/
def toOverTop (A : CommRingCat.{u}) : (Under A)ᵒᵖ ⥤ Over (topObj A) :=
  (Over.opEquivOpUnder A).inverse ⋙ Over.post toTop

/-- The object map of `toOverTop` sends an `A`-algebra to the spectrum of its
underlying ring, as a space over `Spec A`. -/
theorem toOverTop_obj {A : CommRingCat.{u}} (B : Under A) :
    (toOverTop A).obj (op B) = Over.mk (topMap B.hom) :=
  sorry

/-- Spec as a functor from `A`-algebras identifying local rings to spaces over `Spec A`. -/
abbrev toOverTopOnLocalRings (A : CommRingCat.{u}) :
    (RingHom.IsIsoOnLocalRings.Under A)ᵒᵖ ⥤ Over (topObj A) :=
  (MorphismProperty.Under.forget (RingHom.toMorphismProperty RingHom.IsIsoOnLocalRings) ⊤ A).op ⋙
    toOverTop A

/-- The Spec functor on local-ring-identifying algebra maps is bijective on hom sets. -/
theorem toOverTopOnLocalRings_map_bijective {A : CommRingCat.{u}}
    {B C : (RingHom.IsIsoOnLocalRings.Under A)ᵒᵖ} :
    Function.Bijective
      ((toOverTopOnLocalRings A).map :
        (B ⟶ C) → ((toOverTopOnLocalRings A).obj B ⟶ (toOverTopOnLocalRings A).obj C)) :=
  sorry

/-- The functor `toOverTopOnLocalRings` is full. -/
instance toOverTopOnLocalRings.full {A : CommRingCat.{u}} :
    (toOverTopOnLocalRings A).Full :=
  sorry

/-- The functor `toOverTopOnLocalRings` is faithful. -/
instance toOverTopOnLocalRings.faithful {A : CommRingCat.{u}} :
    (toOverTopOnLocalRings A).Faithful :=
  sorry

end AlgebraicGeometry.Spec
