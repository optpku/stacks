module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Unit.Closed

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory.InternalHom.RHom

noncomputable section

universe u

open scoped TensorProduct

namespace CategoryTheory.DerivedCategory.IsRelativeDualizingComplex

/-- A relative dualizing complex has invertible homothety from the regular degree-zero object
to its canonical derived endomorphism object. -/
theorem homothety_isIso
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    [InternalHom.RHom.Has (A := A ⊗[R] A)]
    [InternalHom.RHom.Has (A := A)]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u, u} A))]
    {K : DerivedCategory (ModuleCat.{u, u} A)}
    (hK : IsRelativeDualizingComplex R K)
    (M : ClosedComparison)
    (s : Unit.single ≅
      𝟙_ (DerivedCategory (ModuleCat.{u, u} A))) :
    IsIso (s.hom ≫
      @MonoidalClosed.curry' (DerivedCategory (ModuleCat.{u, u} A)) _ _
        K K (M.closed.closed K) (𝟙 K) ≫
      (M.objIso K K).inv) := sorry

end CategoryTheory.DerivedCategory.IsRelativeDualizingComplex
