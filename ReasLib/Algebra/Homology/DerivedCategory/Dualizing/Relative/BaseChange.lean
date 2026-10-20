module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import ReasLib.Algebra.Category.ModuleCat.Tor.BaseChange
public import ReasLib.RingTheory.Algebra.TensorProduct.FinitePresentation
public import ReasLib.RingTheory.Algebra.TensorProduct.Flat
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative

@[expose] public section

open CategoryTheory
open CategoryTheory.ModuleCat.Tor.Flat.BaseChange
open scoped TensorProduct Algebra.TensorProduct.Right

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

/-- Every flat finitely presented commutative algebra admits a relative dualizing complex. -/
theorem existsRelativeDualizingComplex
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    [InternalHom.RHom.Has (A := A ⊗[R] A)] :
    ∃ K : DerivedCategory (ModuleCat A), IsRelativeDualizingComplex R K := sorry

namespace IsRelativeDualizingComplex

/-- Arbitrary scalar extension preserves relative dualizing complexes of flat finitely presented algebras. -/
theorem baseChange
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    [InternalHom.RHom.Has (A := A ⊗[R] A)]
    (K : DerivedCategory (ModuleCat A)) (hK : IsRelativeDualizingComplex R K)
    (R' : Type u) [CommRing R'] [Algebra R R']
    [InternalHom.RHom.Has (A := (A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))] :
    let A' := A ⊗[R] R'
    let K' := (ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K
    let h_flat : Module.Flat R' A' := Algebra.TensorProduct.flat_right
    let h_finitePresentation : Algebra.FinitePresentation R' A' :=
      Algebra.finitePresentation_tensor_right
    @IsRelativeDualizingComplex R' _ A' _ _ h_flat h_finitePresentation inferInstance K' := sorry

/-- The diagonal object is preserved up to isomorphism by tensor-square scalar extension. -/
theorem baseChangeDiagonalIsomorphic
    (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A] :
    let A' := A ⊗[R] R'
    let B := A ⊗[R] A
    let B' := A' ⊗[R'] A'
    let β : B →+* B' := productMap
      (AlgHom.id R' A') (Algebra.TensorProduct.commRight R R' A).toAlgHom
    let F := ModuleCat.derivedExtensionOfScalars β
    IsIsomorphic
      (F.obj (ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R A)))
      (ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R' A')) := sorry

/-- Tensor-square scalar extension is compatible up to isomorphism with extending a target complex. -/
theorem baseChangeTargetIsomorphic
    (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] (K : DerivedCategory (ModuleCat A)) :
    let A' := A ⊗[R] R'
    let B := A ⊗[R] A
    let B' := A' ⊗[R'] A'
    let β : B →+* B' := productMap
      (AlgHom.id R' A') (Algebra.TensorProduct.commRight R R' A).toAlgHom
    let F := ModuleCat.derivedExtensionOfScalars β
    let K' := (ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj K
    IsIsomorphic
      (F.obj ((ModuleCat.derivedExtensionOfScalars
        (Algebra.TensorProduct.includeLeftRingHom : A →+* B)).obj K))
      ((ModuleCat.derivedExtensionOfScalars
        (Algebra.TensorProduct.includeLeftRingHom : A' →+* B')).obj K') := sorry

/-- A cyclic generator of the diagonal derived-Hom module remains a generator after base change. -/
theorem baseChangeGenerator
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    [InternalHom.RHom.Has (A := A ⊗[R] A)]
    (K : DerivedCategory (ModuleCat A)) (hK : IsRelativeDualizingComplex R K)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    let A' := A ⊗[R] R'
    let B := A ⊗[R] A
    let B' := A' ⊗[R'] A'
    let β : B →+* B' := productMap
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
        Submodule.span B' {eΔ.inv ≫ F.map ξ ≫ eT.hom} = ⊤ := sorry

end IsRelativeDualizingComplex

end CategoryTheory.DerivedCategory
