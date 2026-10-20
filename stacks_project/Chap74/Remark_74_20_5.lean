module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmoothLocal.Properties
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Remark 74.20.5 (1): flat morphisms of algebraic spaces are smooth local on the
source-and-target. -/
@[stacks 06FC] #check
  (AlgebraicGeometry.AlgebraicSpace.Flat.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget (@Flat S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.20.5 (2): morphisms of algebraic spaces that are locally of finite
presentation are smooth local on the source-and-target. -/
@[stacks 06FC] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget
        (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.20.5 (3): morphisms of algebraic spaces that are locally of finite
type are smooth local on the source-and-target. -/
@[stacks 06FC] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget
        (@LocallyOfFiniteType S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.20.5 (4): universally open morphisms of algebraic spaces are smooth
local on the source-and-target. -/
@[stacks 06FC] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget
        (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.20.5 (5): syntomic morphisms of algebraic spaces are smooth local on
the source-and-target. -/
@[stacks 06FC] #check
  (AlgebraicGeometry.AlgebraicSpace.Syntomic.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget
        (@Syntomic S : MorphismProperty (AlgebraicSpace S)))

/- Remark 74.20.5 (6): smooth morphisms of algebraic spaces are smooth local on
the source-and-target. -/
@[stacks 06FC] #check
  (AlgebraicGeometry.AlgebraicSpace.Smooth.isSmoothLocalAtSourceAndTarget :
    ∀ {S : Scheme.{u}},
      IsSmoothLocalAtSourceAndTarget
        (@Smooth S : MorphismProperty (AlgebraicSpace S)))
