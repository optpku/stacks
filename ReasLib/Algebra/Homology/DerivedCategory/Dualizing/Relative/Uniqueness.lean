module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative
import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality.Perfect

@[expose] public section

open CategoryTheory

noncomputable section

universe u

open scoped TensorProduct

namespace CategoryTheory.DerivedCategory.IsRelativeDualizingComplex

/-- Any two relative dualizing complexes for a flat finitely presented commutative algebra
are isomorphic in its derived category of modules. -/
theorem isomorphic
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    [InternalHom.RHom.Has (A := A ⊗[R] A)]
    {K L : DerivedCategory (ModuleCat A)}
    (hK : IsRelativeDualizingComplex R K) (hL : IsRelativeDualizingComplex R L) :
    IsIsomorphic K L := sorry

end CategoryTheory.DerivedCategory.IsRelativeDualizingComplex
