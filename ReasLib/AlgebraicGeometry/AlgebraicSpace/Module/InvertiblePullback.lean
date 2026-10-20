module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Invertible

@[expose] public section
open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The explicit geometric inverse image followed by tensor extension preserves
invertible modules: pull back the local rank-one trivializations. This is a
property of the specified functor, not a producer of a chosen module. -/
instance isInvertibleObject_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (i : X ⟶ Y) (M : Y.Modules) [isInvertibleObject M] :
    isInvertibleObject ((pullback i).obj M) := by
  refine (isInvertibleObject.iff_exists_tensorInverse ((pullback i).obj M)).mpr ?_
  refine ⟨(pullback i).obj (isInvertibleObject.inverse M), ⟨?_⟩, ⟨?_⟩⟩
  · exact (PullbackTensor.tensorIso i M (isInvertibleObject.inverse M)).symm ≪≫
      (pullback i).mapIso (isInvertibleObject.tensorInverseIso M) ≪≫
        PullbackTensor.unitIso i
  · exact (PullbackTensor.tensorIso i (isInvertibleObject.inverse M) M).symm ≪≫
      (pullback i).mapIso (isInvertibleObject.inverseTensorIso M) ≪≫
        PullbackTensor.unitIso i

end AlgebraicGeometry.AlgebraicSpace.Modules
