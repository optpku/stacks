module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.RHom
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
public import ReasLib.RingTheory.PicardGroup.Invertible

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedCoextension

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Invertible R (RingHom.ker (algebraMap R A))]

/-- For a surjective algebra map with invertible kernel, derived coextension is represented by
tensoring with the dual of the base-changed kernel, shifted by `-1`. -/
theorem isomorphicTensorKernelInverse
    (h_surjective : Function.Surjective (algebraMap R A)) :
    IsIsomorphic (derivedCoextensionOfScalars (algebraMap R A))
      (derivedTensorChangeOfRings (algebraMap R A)
        ((shiftFunctor (DerivedCategory (ModuleCat A)) (-1 : ℤ)).obj
          (ModuleCat.single0
            (ModuleCat.of A
              (Module.Dual A (TensorProduct R A (RingHom.ker (algebraMap R A)))))))) := sorry

/-- For every derived module, the kernel comparison identifies the value of derived coextension
with tensoring by the dual of the base-changed kernel shifted by `-1`. -/
theorem objIsomorphicTensorKernelInverse
    (h_surjective : Function.Surjective (algebraMap R A))
    (K : DerivedCategory (ModuleCat R)) :
    IsIsomorphic ((derivedCoextensionOfScalars (algebraMap R A)).obj K)
      ((derivedTensorChangeOfRings (algebraMap R A)
        ((shiftFunctor (DerivedCategory (ModuleCat A)) (-1 : ℤ)).obj
          (ModuleCat.single0
            (ModuleCat.of A
              (Module.Dual A (TensorProduct R A (RingHom.ker (algebraMap R A)))))))).obj K) := sorry

end CategoryTheory.ModuleCat.DerivedCoextension
