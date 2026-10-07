module

public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct.IdealPowerTorsion
import StacksCheckRecall

/-!
# Tensor products with ideal-power torsion

Lemma 15.89.7 transfers a nonpositive derived-tensor bound modulo `I` to powers of `I`,
ideal-power torsion modules, and bounded complexes with ideal-power torsion cohomology.

@stack 0H82
-/

@[expose] public section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

section

variable {R : Type u} [CommRing R]

@[stacks 0H82 "Lemma 15.89.7 (1)"]
#check fun (I : Ideal R) (K : _root_.DerivedCategory (ModuleCat R))
    (hKI : (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I))).IsLE 0) (n : ℕ+) ↦
  (CategoryTheory.DerivedCategory.TensorProduct.IdealPowerTorsion.quotient_isLE_zero
      I K hKI n :
    (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))).IsLE 0)

@[stacks 0H82 "Lemma 15.89.7 (2)"]
#check fun (I : Ideal R) (K : _root_.DerivedCategory (ModuleCat R))
    (hKI : (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I))).IsLE 0)
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) ↦
  (CategoryTheory.DerivedCategory.TensorProduct.IdealPowerTorsion.module_isLE_zero
      I K hKI N hN :
    (K ⊗[R]^L ModuleCat.single0Functor.obj N).IsLE 0)

@[stacks 0H82 "Lemma 15.89.7 (3)"]
#check fun (I : Ideal R) (K : _root_.DerivedCategory (ModuleCat R))
    (hKI : (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I))).IsLE 0)
    (M : _root_.DerivedCategory.Bounded (ModuleCat R))
    (hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat R) i).obj M.obj))
    (hMle : M.obj.IsLE 0) ↦
  (CategoryTheory.DerivedCategory.TensorProduct.IdealPowerTorsion.bounded_isLE_zero
      I K hKI M hMtors hMle :
    (K ⊗[R]^L M.obj).IsLE 0)

@[stacks 0H82 "bounded nonpositive torsion companion"]
#check fun (I : Ideal R) (K : _root_.DerivedCategory (ModuleCat R))
    (hKI : (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I))).IsLE 0)
    (M : _root_.DerivedCategory.Bounded (ModuleCat R))
    (hMtors : ∀ i ≤ 0, Module.IsIdealPowerTorsion I
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat R) i).obj M.obj))
    (hMle : M.obj.IsLE 0) ↦
  (CategoryTheory.DerivedCategory.TensorProduct.IdealPowerTorsion.bounded_isLE_zero_of_nonpositive
      I K hKI M hMtors hMle :
    (K ⊗[R]^L M.obj).IsLE 0)

end
