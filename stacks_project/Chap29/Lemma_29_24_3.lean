/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Lemma 29.24.3 [0CET]: composition of submersive and universally submersive morphisms is
provided by the neutral scheme-morphism API, including typeclass instances. -/
@[stacks 0CET]
#check (AlgebraicGeometry.submersive_comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    AlgebraicGeometry.Submersive f → AlgebraicGeometry.Submersive g →
      AlgebraicGeometry.Submersive (f ≫ g))
#check (AlgebraicGeometry.universallySubmersive_comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    AlgebraicGeometry.UniversallySubmersive f → AlgebraicGeometry.UniversallySubmersive g →
      AlgebraicGeometry.UniversallySubmersive (f ≫ g))
#check (AlgebraicGeometry.instSubmersiveComp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.Submersive f] [AlgebraicGeometry.Submersive g],
      AlgebraicGeometry.Submersive (f ≫ g))
#check (AlgebraicGeometry.instUniversallySubmersiveComp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.UniversallySubmersive f] [AlgebraicGeometry.UniversallySubmersive g],
      AlgebraicGeometry.UniversallySubmersive (f ≫ g))

end AlgebraicGeometry
