module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence.WeakSerre
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : HomologicalComplex₂ C (up ℤ) (up ℤ)} [K.HasTotal (up ℤ)]
variable (hfin : HomologicalComplex₂.AntidiagonalSupport.Finite K)
variable (E₁ E₂ : CohomologicalSpectralSequence C 0)
variable (hAssocFirst : FilteredComplex.IsAssociated
  (HomologicalComplex₂.First.Filtration.total K) E₁)
variable (hAssocSecond : FilteredComplex.IsAssociated
  (HomologicalComplex₂.Second.Filtration.total K) E₂)

/- Lemma 12.25.3 hypothesis [0132]: every antidiagonal contains only finitely many nonzero
bidegrees. -/
@[stacks 0132]
#check (HomologicalComplex₂.AntidiagonalSupport.Finite K : Prop)

/- Lemma 12.25.3 (1) [0132]: the first associated spectral sequence is bounded. -/
@[stacks 0132]
#check (FilteredComplex.HasFiniteFiltrations.Convergence.isBounded_of_associated
  (HomologicalComplex₂.AntidiagonalSupport.Finite.First.hasFiniteFiltrations hfin)
  hAssocFirst : E₁.IsBounded)
/- Lemma 12.25.3 (2) [0132]: the second associated spectral sequence is bounded. -/
@[stacks 0132]
#check (FilteredComplex.HasFiniteFiltrations.Convergence.isBounded_of_associated
  (HomologicalComplex₂.AntidiagonalSupport.Finite.Second.hasFiniteFiltrations hfin)
  hAssocSecond : E₂.IsBounded)

/- Lemma 12.25.3 (3) [0132]: the first induced filtration on total cohomology is finite. -/
@[stacks 0132]
#check (FilteredComplex.HasFiniteFiltrations.Cohomology.isFinite
  (HomologicalComplex₂.AntidiagonalSupport.Finite.First.hasFiniteFiltrations hfin) :
  FilteredComplex.Cohomology.Filtration.IsFinite
    (HomologicalComplex₂.First.Filtration.total K))
/- Lemma 12.25.3 (4) [0132]: the second induced filtration on total cohomology is finite. -/
@[stacks 0132]
#check (FilteredComplex.HasFiniteFiltrations.Cohomology.isFinite
  (HomologicalComplex₂.AntidiagonalSupport.Finite.Second.hasFiniteFiltrations hfin) :
  FilteredComplex.Cohomology.Filtration.IsFinite
    (HomologicalComplex₂.Second.Filtration.total K))

/- Lemma 12.25.3 (5) [0132]: the first associated spectral sequence converges to total
cohomology. -/
@[stacks 0132]
#check (FilteredComplex.HasFiniteFiltrations.Convergence.converges
  (HomologicalComplex₂.AntidiagonalSupport.Finite.First.hasFiniteFiltrations hfin)
  hAssocFirst :
    FilteredComplex.Cohomology.Convergence.Converges
      (HomologicalComplex₂.First.Filtration.total K) E₁)
/- Lemma 12.25.3 (6) [0132]: the second associated spectral sequence converges to total
cohomology. -/
@[stacks 0132]
#check (FilteredComplex.HasFiniteFiltrations.Convergence.converges
  (HomologicalComplex₂.AntidiagonalSupport.Finite.Second.hasFiniteFiltrations hfin)
  hAssocSecond :
    FilteredComplex.Cohomology.Convergence.Converges
      (HomologicalComplex₂.Second.Filtration.total K) E₂)

section Membership

variable (P : ObjectProperty C) [ObjectProperty.IsWeakSerreClass P]
variable {r : ℤ} (hr : (0 : ℤ) ≤ r)
variable (hpageFirst : ∀ p q : ℤ, P ((E₁.page r hr).X (p, q)))
variable (hpageSecond : ∀ p q : ℤ, P ((E₂.page r hr).X (p, q)))

/- Lemma 12.25.3 (7) [0132]: pagewise membership in a weak Serre class for the first spectral
sequence propagates to total cohomology. -/
@[stacks 0132]
#check (FilteredComplex.HasFiniteFiltrations.Cohomology.mem_of_page_mem
  (HomologicalComplex₂.AntidiagonalSupport.Finite.First.hasFiniteFiltrations hfin)
  hAssocFirst P hr hpageFirst :
    ∀ n : ℤ, P ((HomologicalComplex₂.First.Filtration.total K).underlying.homology n))
/- Lemma 12.25.3 (8) [0132]: pagewise membership in a weak Serre class for the second spectral
sequence propagates to total cohomology. -/
@[stacks 0132]
#check (FilteredComplex.HasFiniteFiltrations.Cohomology.mem_of_page_mem
  (HomologicalComplex₂.AntidiagonalSupport.Finite.Second.hasFiniteFiltrations hfin)
  hAssocSecond P hr hpageSecond :
    ∀ n : ℤ, P ((HomologicalComplex₂.Second.Filtration.total K).underlying.homology n))

end Membership
