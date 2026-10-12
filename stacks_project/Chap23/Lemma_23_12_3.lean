/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Filtration.Even.PageOne
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Homology.Odd
import StacksCheckRecall

@[expose] public section

/-!
# Homology after adjoining a variable

Lemma 23.12.3 is derived from the actual chain complex underlying an adjoining-variable DGA. For
a degree-one variable, the attaching cycle, its class `[f]`, multiplication by `[f]`, and the maps
on every `H_n` induced by the base inclusion are canonical data. The odd cell is explicitly the
homotopy cofiber of multiplication by its attaching cycle, giving a canonical short exact complex,
its connecting map, and all three adjacent exact pairs in the resulting long exact sequence. The
terminal `H₀` map is surjective by nonnegativity.

For a degree-two variable, the divided-monomial exponent gives a genuine bounded filtered complex
on the actual even-cell chain DGA. Associated spectral sequences exist and converge; every first
page entry has a canonical isomorphism to the corresponding base homology group, and relative to
association data the actual first differential is multiplication by the attaching class. No
spectral sequence or homology comparison is selected from a deferred existence theorem.
-/

open CategoryTheory CategoryTheory.Limits
open DividedPowerChainAlgebra.Adjoin.Even.Extension.ExponentFiltration
open PageOne

universe u v

section Odd

variable {R : Type u} [CommRing R]
variable {A : DividedPowerChainAlgebra.{u, v} R}
variable {f : A.toChainDGAlgebra.nonnegativePiece 0}
variable (X : DividedPowerChainAlgebra.Adjoin.Odd.Extension A (1 : ℕ+) f)
variable (n : ℕ)

/- Lemma 23.12.3 (1) (Tag 0GZ6): the degree-one odd cell is explicitly the homotopy cofiber of
right multiplication by its attaching cycle. -/
@[stacks 0GZ6 "(1), degree-one odd cell as a homotopy cofiber"]
#check (DividedPowerChainAlgebra.Adjoin.Odd.Extension.cofiberIso X :
  X.algebra.toChainDGAlgebra.toChainComplex ≅ X.cofiber)

/- The comparison first puts every presentation into canonical coefficient coordinates; these
coordinates preserve the base, generator, differential, and multiplication. -/
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.standardModel
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.coefficientEquiv
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.coefficientEquiv_d
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.coefficientEquiv_mul

/- The cofiber presentation gives the canonical short exact complex underlying the long exact
homology sequence. -/
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.shortComplex
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.shortExact
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.boundary_eq_shiftedAttachingMap
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.attachingMap_eq_rightMulCycle
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.homologyMap_attachingMap_eq

/- The chain projection is the signed variable coefficient in every positive degree and is
independent of the chosen cell presentation, as is the resulting short complex. -/
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.Cofiber.signedVariableCoefficient
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.projection_succ
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.Comparison.projection
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.Comparison.shortComplexIso

/- The positive-degree projection closes the long-exact cycle before multiplication by `[f]`. -/
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.homologyProjectionSucc
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.exact_projection_attachingMul

/- Lemma 23.12.3 (1) (Tag 0GZ6): for every `n`, multiplication by `[f]` followed by the
inclusion-induced map `H_n(A) ⟶ H_n(A⟨T⟩)` is an exact pair. -/
@[stacks 0GZ6 "(1), all-degree exact pair after multiplication by the attaching class"]
#check (DividedPowerChainAlgebra.Adjoin.Odd.Extension.exact_attachingMul_inclusion X n :
  Function.Exact (X.attachingClassMulAt n) (X.homologyInclusion n))

/- The inclusion-induced map followed by the projection is the third adjacent exact pair. -/
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.exact_inclusion_projectionSucc

/- The displayed zeroth-homology exact segment is the degree-zero specialization. -/
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.exact_attachingMul_zeroInclusion

/- Lemma 23.12.3 (1), terminal clause: `H₀(A) ⟶ H₀(A⟨T⟩)` is surjective. -/
@[stacks 0GZ6 "(1), terminal zeroth-homology surjectivity"]
#check (DividedPowerChainAlgebra.Adjoin.Odd.Extension.homologyZeroInclusion_surjective X :
  Function.Surjective X.homologyZeroInclusion)

end Odd

section Even

variable {R : Type u} [CommRing R]
variable {A : DividedPowerChainAlgebra.{u, v} R}
variable {f₂ : A.toChainDGAlgebra.nonnegativePiece 1}
variable (X₂ : DividedPowerChainAlgebra.Adjoin.Even.Extension A (2 : ℕ+) f₂)
variable {E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0}
variable (S : FilteredComplex.Association (filteredComplex X₂) E)
variable (k i : ℕ)

/- Lemma 23.12.3 (2) (Tag 0GZ6): the actual degree-two exponent filtration admits a bounded
associated spectral sequence converging to the filtered cochain complex; its negative-degree
homology is identified with cell homology by `filteredComplexHomologyIso`. -/
@[stacks 0GZ6 "(2), bounded convergent exponent spectral sequence"]
#check (PageOne.DegreeTwo.existsBoundedConvergent X₂ :
  ∃ E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0,
    FilteredComplex.IsAssociated (filteredComplex X₂) E ∧ E.IsBounded ∧
      FilteredComplex.Cohomology.Convergence.Converges (filteredComplex X₂) E)

/- Lemma 23.12.3 (2): its first-page entry occupied by `A_k T^[i]` is canonically isomorphic to
`H_k(A)`, with no entrywise comparison supplied by the caller. -/
@[stacks 0GZ6 "(2), canonical first-page entries"]
#check (PageOne.DegreeTwo.entryIso X₂ S k i :
  (E.page 1).X (PageOne.bidegree (2 : ℕ+) k i) ≅
    A.toChainDGAlgebra.homology (k : ℤ))

/- Lemma 23.12.3 (2): under entry identifications, the actual first differential is
multiplication by the degree-one attaching class. -/
@[stacks 0GZ6 "(2), first differential"]
#check (PageOne.DegreeTwo.firstDifferentialSquare X₂ S k i :
  CommSq
    ((E.page 1).d (PageOne.bidegree (2 : ℕ+) k (i + 1))
      (PageOne.bidegree (2 : ℕ+) (k + 1) i))
    ((PageOne.DegreeTwo.entryIso X₂ S k (i + 1)).hom)
    ((PageOne.DegreeTwo.entryIso X₂ S (k + 1) i).hom)
    (PageOne.DegreeTwo.attachingClassMulHom X₂ k))

end Even

#check @DividedPowerChainAlgebra.Adjoin.Cell
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.attachingClassMul
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.attachingClassMulAt
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.homologyInclusion
#check @DividedPowerChainAlgebra.Adjoin.Odd.Extension.homologyZeroInclusion
#check @DividedPowerChainAlgebra.Adjoin.Even.Extension.coefficientEquiv_d
#check @filtration
#check @filteredComplex
#check @filteredComplexHomologyIso
#check @hasFiniteFiltrations
#check @gradedPieceIso
#check @PageOne.Entry.termIso
#check @PageOne.Entry.complexIso
#check @PageOne.Entry.homologyIso
#check @PageOne.Entry.iso
#check @PageOne.Entry.differential
#check @PageOne.Differential.lowerCoefficient_eq_cyclesMul
#check @coeffDifferential_sameExponent
#check @CategoryTheory.FilteredComplex.IsAssociated.exists
#check @CategoryTheory.FilteredComplex.Association.pageOneIso
#check @CategoryTheory.FilteredComplex.RaisesFiltration.Page.One.homologyIso
#check @CategoryTheory.FilteredComplex.Page.One.d_eq_raisedGradedPieceMap
#check @CategoryTheory.FilteredComplex.HasFiniteFiltrations.Convergence.converges
