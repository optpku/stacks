module

import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal.Splitting
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.32.16: an immersion over `S` that locally has a retraction has a locally split
canonical conormal-differentials complex. -/
@[stacks 0474] #check
  (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.locallySplit_of_locallyHasRetraction :
    ∀ {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S),
      AlgebraicGeometry.Scheme.Hom.LocallyHasRetractionOver i f →
        AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.IsLocallySplit i f)

#check
  (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.complex_splitting_of_hasRetraction :
    ∀ {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S),
      AlgebraicGeometry.Scheme.Hom.HasRetractionOver i f →
        Nonempty
          ((AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.complex i f).Splitting))

#check
  (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.map_isIso_of_section :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (s : S ⟶ X), s ≫ f = 𝟙 S →
      IsIso (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.map s f))
