module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Flattening
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent] (T : SchemeOver Y)

/- 77.7.8.1: the contravariant flattening functor on schemes over `Y` is singleton
precisely when the base change of `ℱ` is flat over the test scheme, and empty otherwise. -/
@[stacks 0CWY] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.functor f ℱ : (SchemeOver Y)ᵒᵖ ⥤ Type u)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.functor_obj_nonempty_iff f ℱ T :
    Nonempty ((AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.functor f ℱ).obj (op T)) ↔
      AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.isFlat f ℱ T)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.functor_obj_isEmpty_iff f ℱ T :
    IsEmpty ((AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.functor f ℱ).obj (op T)) ↔
      ¬ AlgebraicGeometry.AlgebraicSpace.Modules.Flattening.isFlat f ℱ T)
