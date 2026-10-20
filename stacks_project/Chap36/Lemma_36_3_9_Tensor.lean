module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor.Right
public import stacks_project.Chap36.Lemma_36_3_9_Instances

@[expose] public section

open CategoryTheory DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- The quasicoherent fixed-right tensor API is provided by its shared mathematical owner. -/
#check (tensorRight.mapsTo :
  ∀ {X : Scheme.{u}}
    (L : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)),
    DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).inverseImage
          (DerivedTensor.Right.functor L.obj))

end AlgebraicGeometry.Scheme.DerivedQCoh
