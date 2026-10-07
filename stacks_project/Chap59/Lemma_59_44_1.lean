module

import StacksCheckRecall
public import stacks_project.Chap59.Lemma_59_44_1_PropertyC
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Reflection

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

/- Lemma 59.44.1 (1): under Property (C), the small étale direct image
reflects injections, expressed as reflection of monomorphisms. -/
@[stacks 04DT] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism_pushforward_reflectsMonomorphisms_of_hasPropertyC :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology (Type (u + 1))]
      (hC : hasPropertyC f),
      (smallMorphism f).pushforward.ReflectsMonomorphisms)

/- Lemma 59.44.1 (2): under Property (C), the small étale direct image
reflects surjections, expressed as reflection of epimorphisms. -/
@[stacks 04DT] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism_pushforward_reflectsEpimorphisms_of_hasPropertyC :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology (Type (u + 1))]
      [HasSheafify Y.smallEtaleTopology (Type (u + 1))]
      (hC : hasPropertyC f),
      (smallMorphism f).pushforward.ReflectsEpimorphisms)
