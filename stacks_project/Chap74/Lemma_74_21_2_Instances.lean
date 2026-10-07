module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap74.Definition_74_21_1_EtaleSmoothLocal
public import stacks_project.Chap74.Lemma_74_10_2_BaseChange

/-!
# Étale-smooth locality implications

A morphism property of algebraic spaces that is étale-smooth local on
source-and-target is étale local on the source, smooth local on the target,
stable under postcomposition with étale morphisms, and descends along étale
postcomposition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget

variable {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}

/-- A morphism property that is étale-smooth local on source-and-target is local
for étale covers of the source. -/
instance toIsLocalAtSource [IsEtaleSmoothLocalAtSourceAndTarget P] :
    P.IsLocalAtSource (@etalePrecoverage S) :=
  sorry

/-- A morphism property that is étale-smooth local on source-and-target is local
for smooth covers of the target. -/
instance toIsLocalAtTarget [IsEtaleSmoothLocalAtSourceAndTarget P] :
    P.IsLocalAtTarget (smoothPrecoverage S) :=
  sorry

/-- A morphism property that is étale-smooth local on source-and-target is
preserved by postcomposition with an étale morphism. -/
instance toRespectsRightEtale [IsEtaleSmoothLocalAtSourceAndTarget P] :
    P.RespectsRight (@Etale S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- A morphism property that is étale-smooth local on source-and-target descends
along postcomposition with an étale morphism. -/
instance toHasOfPostcompEtale [IsEtaleSmoothLocalAtSourceAndTarget P] :
    P.HasOfPostcompProperty (@Etale S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- If `f` has an étale-smooth-local-on-source-and-target property and `g` is
étale, then `f ≫ g` has the property. -/
theorem postcomp [IsEtaleSmoothLocalAtSourceAndTarget P] {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : P f) (hg : Etale g) : P (f ≫ g) :=
  sorry

/-- If `g` is étale and `f ≫ g` has an étale-smooth-local-on-source-and-target
property, then `f` has the property. -/
theorem of_postcomp [IsEtaleSmoothLocalAtSourceAndTarget P]
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : Etale g)
    (hfg : P (f ≫ g)) : P f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget
