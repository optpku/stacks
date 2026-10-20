module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DerivedTensorChangeOfRings

noncomputable section

universe u

open scoped TensorProduct

/- Lemma 47.27.6: the derived tensor product of relative dualizing complexes for two
successive flat finitely presented ring maps is relative dualizing for their composite. -/
@[stacks 0E2H]
#check (CategoryTheory.DerivedCategory.IsRelativeDualizingComplex.trans :
  ∀ {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.Flat R A] [Module.Flat A B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation A B]
    [CategoryTheory.DerivedCategory.InternalHom.RHom.Has (A := A ⊗[R] A)]
    [CategoryTheory.DerivedCategory.InternalHom.RHom.Has (A := B ⊗[A] B)]
    [CategoryTheory.DerivedCategory.InternalHom.RHom.Has (A := B ⊗[R] B)]
    {KAR : DerivedCategory (ModuleCat A)}
    {KBA : DerivedCategory (ModuleCat B)},
    CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R KAR →
      CategoryTheory.DerivedCategory.IsRelativeDualizingComplex A KBA →
      @CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R _ B _ _
        (Module.Flat.trans R A B)
        (Algebra.FinitePresentation.trans R A B) inferInstance (KAR ⊗[A]^L[B] KBA))
