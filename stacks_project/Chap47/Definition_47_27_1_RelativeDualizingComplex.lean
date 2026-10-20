module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative

universe u

open scoped TensorProduct

/- Compatibility check for the shared relative dualizing-complex predicate. -/
#check (CategoryTheory.DerivedCategory.IsRelativeDualizingComplex :
  ∀ (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    [CategoryTheory.DerivedCategory.InternalHom.RHom.Has (A := A ⊗[R] A)],
    _root_.DerivedCategory (ModuleCat A) → Prop)
