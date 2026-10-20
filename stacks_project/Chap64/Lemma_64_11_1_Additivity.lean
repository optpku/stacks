module

public import ReasLib.CategoryTheory.Filtration.Complex.FiniteProjective.Trace
public import ReasLib.CategoryTheory.Filtration.Derived.Perfect.Trace
import StacksCheckRecall

open CategoryTheory
open scoped FilteredObject.Finite Ring

universe u

/- Lemma 64.11.1 (Additivity). Let `K` be a perfect object of `DF(ModuleCat Λ)` and
`f` an endomorphism of `K` in `DF`. Then `Tr(f|_K)`, the perfect-complex trace
`DerivedCategory.IsPerfect.traceNatural` of `(Forget.canonicalLift _).map f` in `Λ♮`,
equals `∑ᶠ p, Tr(f|_{gr^p K})`, the finsum of the traces of the induced maps
`(GradedPiece.canonicalLift _ p).map f` on associated graded pieces. -/

@[stacks 03TK] #check
  (CategoryTheory.FilteredObject.FiniteDerived.IsPerfect.traceNatural_eq_sum_gradedPiece :
    ∀ {Λ : Type u} [Ring Λ]
      [HasDerivedCategory (GradedObject ℤ (ModuleCat.{u} Λ))]
      {K : FilteredObject.FiniteDerived.Quotient.Category (ModuleCat.{u} Λ)}
      (hK : FilteredObject.FiniteDerived.IsPerfect K) (f : End K),
      (hK.forget).traceNatural
          ((FilteredObject.FiniteDerived.Forget.canonicalLift (ModuleCat.{u} Λ)).map f) =
        ∑ᶠ p, (hK.gradedPiece p).traceNatural
          ((FilteredObject.FiniteDerived.GradedPiece.canonicalLift (ModuleCat.{u} Λ) p).map f))

#check
  (CategoryTheory.FilteredObject.FiniteDerived.IsPerfect.traceNatural_gradedPiece_finiteSupport :
    ∀ {Λ : Type u} [Ring Λ]
      [HasDerivedCategory (GradedObject ℤ (ModuleCat.{u} Λ))]
      {K : FilteredObject.FiniteDerived.Quotient.Category (ModuleCat.{u} Λ)}
      (hK : FilteredObject.FiniteDerived.IsPerfect K) (f : End K),
      (Function.support fun p : ℤ ↦
        (hK.gradedPiece p).traceNatural
          ((FilteredObject.FiniteDerived.GradedPiece.canonicalLift (ModuleCat.{u} Λ) p).map f)).Finite)

#check (CochainComplex.IsBoundedFilteredFiniteProjective.traceNatural_eq_sum_gradedPiece :
    ∀ {Λ : Type u} [Ring Λ] {P : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ}
      [CochainComplex.IsBoundedFilteredFiniteProjective P] (f : P ⟶ P),
      CochainComplex.IsBoundedFiniteProjective.traceNatural
          ((FilteredObject.Finite.Forget.cochain (ModuleCat.{u} Λ)).map f) =
        ∑ᶠ p : ℤ, CochainComplex.IsBoundedFiniteProjective.traceNatural
          ((FilteredObject.Finite.GradedPiece.cochain p).map f))

#check (CochainComplex.IsBoundedFilteredFiniteProjective.traceNatural_gradedPiece_finiteSupport :
    ∀ {Λ : Type u} [Ring Λ] {P : CochainComplex (Filᶠ(ModuleCat.{u} Λ)) ℤ}
      [CochainComplex.IsBoundedFilteredFiniteProjective P] (f : P ⟶ P),
      (Function.support fun p : ℤ ↦
        CochainComplex.IsBoundedFiniteProjective.traceNatural
          ((FilteredObject.Finite.GradedPiece.cochain p).map f)).Finite)
