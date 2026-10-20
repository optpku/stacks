module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Filtration.Trace

@[expose] public section

open CategoryTheory CategoryTheory.Limits FilteredObject ModuleCat Ring
open FilteredObject.Finite
open scoped FilteredObject.Finite Ring ZeroObject

universe u v

variable {Λ : Type u} [Ring Λ]

/- Lemma 64.11.2. The trace of a filtered finite-projective endomorphism is the
sum of its associated graded traces. -/
@[stacks 03TL] #check (CategoryTheory.FilteredObject.Finite.traceNatural_eq_sum_gradedPiece :
    ∀ (P : Filᶠ(ModuleCat.{v} Λ)) [IsFilteredFiniteProjective P.obj]
    (f : P ⟶ P),
    LinearMap.FiniteProjective.traceNatural
        (ModuleCat.Hom.hom ((Forget.functor (ModuleCat.{v} Λ)).map f)) =
      ∑ᶠ p : ℤ, LinearMap.FiniteProjective.traceNatural
        (ModuleCat.Hom.hom (f.hom.gradedPieceMap p)))

#check (CategoryTheory.FilteredObject.Finite.traceNatural_eq_sum_gradedPiece_Ico :
    ∀ (P : Filᶠ(ModuleCat.{v} Λ)) [IsFilteredFiniteProjective P.obj]
    (f : P ⟶ P) {a b : ℤ}
    (ha : IndexedFiltration.stage P.obj.filtration a = ⊤)
    (hb : IndexedFiltration.stage P.obj.filtration b = ⊥),
    LinearMap.FiniteProjective.traceNatural
        (ModuleCat.Hom.hom ((Forget.functor (ModuleCat.{v} Λ)).map f)) =
      ∑ p ∈ Finset.Ico a b,
        LinearMap.FiniteProjective.traceNatural
          (ModuleCat.Hom.hom (f.hom.gradedPieceMap p)))

#check (CategoryTheory.FilteredObject.Finite.traceNatural_gradedPiece_finiteSupport :
    ∀ (P : Filᶠ(ModuleCat.{v} Λ)) [IsFilteredFiniteProjective P.obj]
    (f : P ⟶ P),
    (Function.support fun p : ℤ ↦
        LinearMap.FiniteProjective.traceNatural
          (ModuleCat.Hom.hom (f.hom.gradedPieceMap p))).Finite)
