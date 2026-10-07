module

public import ReasLib.CategoryTheory.Homology.ExactCouple.Bockstein
import StacksCheckRecall

/-!
# Definition 12.22.5

The reusable Bockstein exact-couple construction is owned by
`ReasLib.CategoryTheory.Homology.ExactCouple.Bockstein`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : HomologicalComplex C (ComplexShape.refl PUnit.{1})}
variable (α : A ⟶ A) [Mono α]
variable (K : ExactCouple.Derived.Construction C)

/- Definition 12.22.5 [011Z]: the exact couple associated to the quotient short exact sequence
`A ⟶ A ⟶ cokernel α`, its zero-based spectral sequence, and its zero-page cycle and boundary
filtrations are provided by the generic Bockstein owner. -/
@[stacks 011Z]
#check (HomologicalComplex.Bockstein.spectralSequence α
  (HomologicalComplex.Bockstein.quotientShortExact α) K :
  SpectralSequence C (fun _ : ℤ ↦ ComplexShape.refl PUnit.{1}) 0)

#check HomologicalComplex.Bockstein.quotientShortComplex
#check HomologicalComplex.Bockstein.quotientShortExact
#check HomologicalComplex.Bockstein.connecting
#check HomologicalComplex.Bockstein.exactCouple
#check HomologicalComplex.Bockstein.page_zero
#check HomologicalComplex.Bockstein.page_one
#check SpectralSequence.Page.Zero.ofOne
#check HomologicalComplex.Bockstein.ZeroPage.cycles
#check (ShortComplex.Cycles.toHomology ((cokernel α).sc PUnit.unit) :
  (HomologicalComplex.Bockstein.ZeroPage.cycles α : C) ⟶
    HomologicalComplex.homology (cokernel α) PUnit.unit)
#check @ShortComplex.Cycles.preimageOfIso
#check @HomologyPageTower.preimageCycle
#check @HomologyPageTower.preimageBoundary
#check HomologyPageTower.pageIndex
#check (HomologicalComplex.Bockstein.cycle α
  (HomologicalComplex.Bockstein.quotientShortExact α) K)
#check (HomologicalComplex.Bockstein.boundary α
  (HomologicalComplex.Bockstein.quotientShortExact α) K)

end CategoryTheory
