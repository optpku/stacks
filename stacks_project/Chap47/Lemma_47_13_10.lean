module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.InvertibleKernel
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 47.13.10: for a surjective map `R ⟶ A` with invertible kernel, derived
coextension is represented by tensoring with the inverse of the base-changed kernel,
shifted by `-1`. -/
@[stacks 0BZH] #check
  (CategoryTheory.ModuleCat.DerivedCoextension.isomorphicTensorKernelInverse :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [Module.Invertible R (RingHom.ker (algebraMap R A))],
      Function.Surjective (algebraMap R A) →
      CategoryTheory.IsIsomorphic
        (CategoryTheory.ModuleCat.derivedCoextensionOfScalars (algebraMap R A))
        (CategoryTheory.derivedTensorChangeOfRings (algebraMap R A)
          ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat A)) (-1 : ℤ)).obj
            (ModuleCat.single0
              (ModuleCat.of A
                (Module.Dual A (TensorProduct R A (RingHom.ker (algebraMap R A)))))))))

/- Objectwise form of the derived coextension--tensor identification. -/
#check
  (CategoryTheory.ModuleCat.DerivedCoextension.objIsomorphicTensorKernelInverse :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [Module.Invertible R (RingHom.ker (algebraMap R A))]
      (h_surjective : Function.Surjective (algebraMap R A))
      (K : DerivedCategory (ModuleCat R)),
      CategoryTheory.IsIsomorphic
        ((CategoryTheory.ModuleCat.derivedCoextensionOfScalars (algebraMap R A)).obj K)
        ((CategoryTheory.derivedTensorChangeOfRings (algebraMap R A)
          ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat A)) (-1 : ℤ)).obj
            (ModuleCat.single0
              (ModuleCat.of A
                (Module.Dual A (TensorProduct R A (RingHom.ker (algebraMap R A)))))))).obj K))
