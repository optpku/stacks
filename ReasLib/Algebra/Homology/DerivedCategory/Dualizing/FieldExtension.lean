module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.RelativeDualizing
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Uniqueness

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- Derived extension along a field extension preserves dualizing complexes of finite-type
algebras. -/
theorem baseChange_of_fieldExtension
    {k K A : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} (A ⊗[k] K)))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A)))
    (HAK : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} (A ⊗[k] K))))
    (ω : DerivedCategory (ModuleCat.{u, u} A)) :
    let hA : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
    let hAK : IsNoetherianRing (A ⊗[k] K) :=
      Algebra.FiniteType.isNoetherianRing_tensor_left
    @DerivedCategory.IsDualizingComplex A _ hA _ ω HA →
      @DerivedCategory.IsDualizingComplex (A ⊗[k] K) _ hAK _
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[k] K))).obj ω) HAK := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
