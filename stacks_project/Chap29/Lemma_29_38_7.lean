module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.Criteria
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
variable [AlgebraicGeometry.QuasiCompact f]
variable [AlgebraicGeometry.Scheme.Modules.Invertible L]

/- Lemma 29.38.7
For a quasi-compact morphism and an invertible module, relative very ampleness is equivalent to
relative very ampleness on a base-open cover, to a degree-one-generated graded-algebra
presentation whose associated relative projective morphism is an immersion, and to
quasi-separatedness together with an epic canonical pushforward counit whose classified
projective-bundle morphism is an immersion.
-/
@[stacks 01VR] #check
  (AlgebraicGeometry.relativelyVeryAmple_tfae f L :
    List.TFAE [
      AlgebraicGeometry.RelativelyVeryAmple f L,
      AlgebraicGeometry.RelativelyVeryAmpleOnBaseOpenCover f L,
      AlgebraicGeometry.HasDegreeOneGeneratedImmersionRelativeProjSectionMap f L,
      AlgebraicGeometry.HasCanonicalPushforwardImmersion f L])
