/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Remark_74_20_5_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Remark 74.20.5 (1): flat morphisms of algebraic spaces are smooth local on the
source-and-target. -/
@[stacks 06FC] #check
  (Flat.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget (@Flat S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.20.5 (2): morphisms of algebraic spaces that are locally of finite
presentation are smooth local on the source-and-target. -/
@[stacks 06FC] #check
  (LocallyOfFinitePresentation.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget
        (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.20.5 (3): morphisms of algebraic spaces that are locally of finite
type are smooth local on the source-and-target. -/
@[stacks 06FC] #check
  (LocallyOfFiniteType.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget
        (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.20.5 (4): universally open morphisms of algebraic spaces are smooth
local on the source-and-target. -/
@[stacks 06FC] #check
  (UniversallyOpen.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget
        (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.20.5 (5): syntomic morphisms of algebraic spaces are smooth local on
the source-and-target. -/
@[stacks 06FC] #check
  (Syntomic.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget
        (@Syntomic S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.20.5 (6): smooth morphisms of algebraic spaces are smooth local on
the source-and-target. -/
@[stacks 06FC] #check
  (Smooth.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget
        (@Smooth S : MorphismProperty (AlgebraicSpace S)))
