module

public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct.IdealPowerTorsion
import StacksCheckRecall

/-!
# Tensor products with ideal-power torsion

Lemma 15.89.8 upgrades the bounds of Lemma 15.89.7 to zero-object statements for powers of
`I`, ideal-power torsion modules, and bounded complexes with ideal-power torsion cohomology.

@stack 0G1T
-/

@[expose] public section

open CategoryTheory Limits
open scoped DerivedTensorProduct

universe u

section

variable {R : Type u} [CommRing R]

@[stacks 0G1T "Lemma 15.89.8 (1)"]
#check fun (I : Ideal R) (K : _root_.DerivedCategory (ModuleCat R))
    (hKI : IsZero (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I)))) (n : ℕ+) ↦
  (CategoryTheory.DerivedCategory.TensorProduct.IdealPowerTorsion.quotient_isZero
      I K hKI n :
    IsZero (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))))

@[stacks 0G1T "Lemma 15.89.8 (2)"]
#check fun (I : Ideal R) (K : _root_.DerivedCategory (ModuleCat R))
    (hKI : IsZero (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I))))
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) ↦
  (CategoryTheory.DerivedCategory.TensorProduct.IdealPowerTorsion.module_isZero
      I K hKI N hN :
    IsZero (K ⊗[R]^L ModuleCat.single0Functor.obj N))

@[stacks 0G1T "Lemma 15.89.8 (3)"]
#check fun (I : Ideal R) (K : _root_.DerivedCategory (ModuleCat R))
    (hKI : IsZero (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I))))
    (M : _root_.DerivedCategory.Bounded (ModuleCat R))
    (hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat R) i).obj M.obj)) ↦
  (CategoryTheory.DerivedCategory.TensorProduct.IdealPowerTorsion.bounded_isZero
      I K hKI M hMtors :
    IsZero (K ⊗[R]^L M.obj))

end
