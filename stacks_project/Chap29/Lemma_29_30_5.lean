module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Smooth
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/- Lemma 29.30.5: any open immersion is syntomic. -/
@[stacks 01UJ] #check
  (AlgebraicGeometry.instSyntomicOfSmooth (f := f) : AlgebraicGeometry.Syntomic f)
