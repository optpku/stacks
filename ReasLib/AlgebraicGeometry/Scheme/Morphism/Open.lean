/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.RingTheory.Ideal.GoingDown

@[expose] public section

open CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- An open morphism of schemes lifts generalizations of points. -/
theorem generalizingMap_of_isOpenMap
    (hopen : IsOpenMap f.base) :
    topologically GeneralizingMap f := sorry

/-- Every base change of a universally open morphism of schemes lifts generalizations of points. -/
theorem universallyGeneralizing_of_universallyOpen
    [UniversallyOpen f] :
    (topologically GeneralizingMap).universally f := by
  intro X' Y' i₁ i₂ f' hf'
  exact generalizingMap_of_isOpenMap
    (UniversallyOpen.universally_isOpenMap i₁ i₂ f' hf')

/-- A locally finitely presented morphism that lifts generalizations after every base change is
universally open. -/
theorem universallyOpen_of_universallyGeneralizing
    [LocallyOfFinitePresentation f]
    (hgeneralizing : (topologically GeneralizingMap).universally f) :
    UniversallyOpen f := sorry

end AlgebraicGeometry
