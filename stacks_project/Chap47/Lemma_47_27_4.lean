module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative.BaseChange
import StacksCheckRecall

universe u

open CategoryTheory
open CategoryTheory.ModuleCat.Tor.Flat.BaseChange
open scoped TensorProduct Algebra.TensorProduct.Right

/- Lemma 47.27.4 (1) -/
@[stacks 0E2F] #check (CategoryTheory.DerivedCategory.existsRelativeDualizingComplex :
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A],
    ∃ K : DerivedCategory (ModuleCat A),
      CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R K)

/- Lemma 47.27.4 (2) -/
@[stacks 0E2F] #check (CategoryTheory.DerivedCategory.IsRelativeDualizingComplex.baseChange :
  ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A))
    (hK : CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R K)
    (R' : Type u) [CommRing R'] [Algebra R R'],
    let A' := A ⊗[R] R'
    let K' := (ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K
    let h_flat : Module.Flat R' A' := Algebra.TensorProduct.flat_right
    let h_finitePresentation : Algebra.FinitePresentation R' A' :=
      Algebra.finitePresentation_tensor_right
    @CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R' _ A' _ _ h_flat
      h_finitePresentation K')

/- Lemma 47.27.4 (3) -/
@[stacks 0E2F] #check (CategoryTheory.DerivedCategory.IsRelativeDualizingComplex.baseChangeGenerator :
  ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A))
    (hK : CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R K)
    (R' : Type u) [CommRing R'] [Algebra R R'],
    let A' := A ⊗[R] R'
    let B := A ⊗[R] A
    let B' := A' ⊗[R'] A'
    let β : B →+* B' := CategoryTheory.ModuleCat.Tor.Flat.BaseChange.productMap
      (AlgHom.id R' A') (Algebra.TensorProduct.commRight R R' A).toAlgHom
    let F := ModuleCat.derivedExtensionOfScalars β
    let K' := (ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K
    let Δ := ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R A)
    let T := (ModuleCat.derivedExtensionOfScalars
      (Algebra.TensorProduct.includeLeftRingHom : A →+* B)).obj K
    let Δ' := ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R' A')
    let T' := (ModuleCat.derivedExtensionOfScalars
      (Algebra.TensorProduct.includeLeftRingHom : A' →+* B')).obj K'
    ∀ (ξ : Δ ⟶ T), Submodule.span B {ξ} = ⊤ →
      ∃ (eΔ : F.obj Δ ≅ Δ') (eT : F.obj T ≅ T'),
        Submodule.span B' {eΔ.inv ≫ F.map ξ ≫ eT.hom} = ⊤)

#check (CategoryTheory.DerivedCategory.IsRelativeDualizingComplex.baseChangeDiagonalIsomorphic :
  ∀ (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A],
    let A' := A ⊗[R] R'
    let B := A ⊗[R] A
    let B' := A' ⊗[R'] A'
    let β : B →+* B' := CategoryTheory.ModuleCat.Tor.Flat.BaseChange.productMap
      (AlgHom.id R' A') (Algebra.TensorProduct.commRight R R' A).toAlgHom
    let F := ModuleCat.derivedExtensionOfScalars β
    IsIsomorphic
      (F.obj (ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R A)))
      (ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R' A')))

#check (CategoryTheory.DerivedCategory.IsRelativeDualizingComplex.baseChangeTargetIsomorphic :
  ∀ (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (K : DerivedCategory (ModuleCat A)),
    let A' := A ⊗[R] R'
    let B := A ⊗[R] A
    let B' := A' ⊗[R'] A'
    let β : B →+* B' := CategoryTheory.ModuleCat.Tor.Flat.BaseChange.productMap
      (AlgHom.id R' A') (Algebra.TensorProduct.commRight R R' A).toAlgHom
    let F := ModuleCat.derivedExtensionOfScalars β
    let K' := (ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K
    IsIsomorphic
      (F.obj ((ModuleCat.derivedExtensionOfScalars
        (Algebra.TensorProduct.includeLeftRingHom : A →+* B)).obj K))
      ((ModuleCat.derivedExtensionOfScalars
        (Algebra.TensorProduct.includeLeftRingHom : A' →+* B')).obj K'))
