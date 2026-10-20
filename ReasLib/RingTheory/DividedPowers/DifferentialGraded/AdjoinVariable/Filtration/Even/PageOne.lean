module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.HomologyAlgebra
public import ReasLib.CategoryTheory.Filtration.Complex.PageOne
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.AdjoinVariable.Filtration.Even.Homology

/-!
# The first page of the exponent filtration on an even cell

This leaf connects the explicit exponent filtration on an even divided-power cell to the generic
spectral-sequence API.  It does not select a spectral sequence.  Instead it records existence,
boundedness, and convergence as propositions, and states first-page comparisons relative to
given association data.

For an exponent `i`, the decreasing filtration degree is `-i`.  A base class in chain degree
`k`, multiplied by `T^[i]`, lies in cochain total degree `-(k + i * d)`.  The general API works
for every positive even cell degree `d`; the `DegreeTwo` namespace contains the specialization
corresponding to Stacks Project Tag 0GZ6.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace DividedPowerChainAlgebra.Adjoin.Even.Extension.ExponentFiltration
namespace PageOne

variable {R : Type u} [CommRing R]
variable {A : DividedPowerChainAlgebra.{u, v} R} {d : ℕ+}
variable {f : A.toChainDGAlgebra.nonnegativePiece ((d : ℕ) - 1)}

/-! ## Bidegree conventions -/

/-- The decreasing filtration degree corresponding to divided-monomial exponent `i`. -/
def filtrationDegree (i : ℕ) : ℤ := -(i : ℤ)

/-- The cochain total degree of a base degree-`k` coefficient multiplying `T^[i]`. -/
def totalDegree (d : ℕ+) (k i : ℕ) : ℤ := -((k + i * (d : ℕ) : ℕ) : ℤ)

/-- The first-page bidegree of a base degree-`k` coefficient multiplying `T^[i]`. -/
def bidegree (d : ℕ+) (k i : ℕ) : ℤ × ℤ :=
  (filtrationDegree i, totalDegree d k i - filtrationDegree i)

/-- The two coordinates of `bidegree d k i` add to its cochain total degree. -/
theorem bidegree_total (d : ℕ+) (k i : ℕ) :
    (bidegree d k i).1 + (bidegree d k i).2 = totalDegree d k i := sorry

/-- Lowering the exponent by one and applying a cochain differential preserves the second
first-page coordinate and raises the first coordinate by one. -/
theorem bidegree_lowerExponent (d : ℕ+) (k i : ℕ) :
    ((bidegree d k (i + 1)).1 + 1, (bidegree d k (i + 1)).2) =
      bidegree d (((d : ℕ) - 1) + k) i := sorry

/-! ## Graded-piece entries -/

namespace Entry

/-- The degree function of the fixed-exponent embedding is injective. -/
theorem embedding_injective (d : ℕ+) (i : ℕ) :
    Function.Injective (fun k : ℕ ↦ totalDegree d k i) := sorry

/-- The fixed-exponent degree function sends chain adjacency to cochain adjacency. -/
theorem embedding_rel (d : ℕ+) (i : ℕ) {k l : ℕ}
    (h : (ComplexShape.down ℕ).Rel k l) :
    (ComplexShape.up ℤ).Rel (totalDegree d k i) (totalDegree d l i) := sorry

/-- The affine embedding which places base chain degree `k` in the cochain degree occupied by
the coefficient of `T^[i]`. -/
@[stacks 0GZ6 "degree embedding for one exponent"]
def embedding (d : ℕ+) (i : ℕ) :
    ComplexShape.Embedding (ComplexShape.down ℕ) (ComplexShape.up ℤ) where
  f k := totalDegree d k i
  injective_f := embedding_injective d i
  rel := embedding_rel d i

/-- The fixed-exponent embedding preserves and reflects adjacent degrees. -/
instance embeddingIsRelIff (d : ℕ+) (i : ℕ) :
    (embedding d i).IsRelIff := sorry

/-- The image of the fixed-exponent embedding is closed under predecessors. -/
instance embeddingIsTruncLE (d : ℕ+) (i : ℕ) :
    (embedding d i).IsTruncLE := sorry

/-- The fixed-exponent graded-piece complex, indexed by the base chain degree. -/
@[stacks 0GZ6 "complex carried by one exponent"]
def complex (X : Even.Extension A d f) (i : ℕ) :
    ChainComplex (ModuleCat.{v} R) ℕ :=
  ((filteredComplex X).gradedPiece (filtrationDegree i)).restriction (embedding d i)

/-- Taking a graded piece after extension from natural chain degrees is canonically identified
with taking that graded piece before extension. -/
@[stacks 0GZ6 "graded-piece extension comparison"]
def extensionIso (X : Even.Extension A d f) (m : ℕ) (p : ℤ) :
    ((filteredComplex X).gradedPiece p).X (-(m : ℤ)) ≅
      ((filtration X).term m).gradedPiece p :=
  (FilteredObject.associatedGradedFunctor ⋙ GradedObject.eval p).mapIso
    ((filteredNatComplex X).extendXIso ComplexShape.embeddingDownNat rfl)

/-- In cochain degree `-(k + i * d)`, the exponent-`i` graded piece is the base degree-`k`
module. -/
@[stacks 0GZ6 "coefficient term comparison on one exponent"]
def termIso (X : Even.Extension A d f) (k i : ℕ) :
    ((filteredComplex X).gradedPiece (filtrationDegree i)).X (totalDegree d k i) ≅
      ModuleCat.of R (A.toChainDGAlgebra.nonnegativePiece k) :=
  extensionIso X (k + i * (d : ℕ)) (filtrationDegree i) ≪≫
    gradedPieceIso X k i

/-- The term comparison regarded as an isomorphism from the fixed-exponent complex to the
natural-degree restriction of the base DGA. -/
@[stacks 0GZ6 "fixed-exponent component comparison"]
def componentIso (X : Even.Extension A d f) (k i : ℕ) :
    (complex X i).X k ≅ A.toChainDGAlgebra.natRestriction.X k :=
  termIso X k i ≪≫ (A.toChainDGAlgebra.natRestrictionXIso k).symm

/-- The cochain differential on a fixed exponent graded piece is the base chain differential
under the termwise coefficient identifications. -/
theorem differential (X : Even.Extension A d f) (k i : ℕ) :
    ((filteredComplex X).gradedPiece (filtrationDegree i)).d
        (totalDegree d (k + 1) i) (totalDegree d k i) ≫
      (termIso X k i).hom =
    (termIso X (k + 1) i).hom ≫
      ModuleCat.ofHom
        (A.toChainDGAlgebra.nonnegativeDifferential ⟨k + 1, Nat.zero_lt_succ k⟩) := sorry

/-- The component comparisons commute with the differentials of the fixed-exponent and base
complexes. -/
theorem componentIso_d (X : Even.Extension A d f) (i : ℕ) (k l : ℕ)
    (hkl : (ComplexShape.down ℕ).Rel k l) :
    (componentIso X k i).hom ≫ A.toChainDGAlgebra.natRestriction.d k l =
      (complex X i).d k l ≫ (componentIso X l i).hom := sorry

/-- The exponent-`i` graded-piece complex is canonically the natural-degree restriction of the
base DGA.  Its data is assembled from `termIso`; differential compatibility is proof-only. -/
@[stacks 0GZ6 "fixed-exponent complex comparison"]
def complexIso (X : Even.Extension A d f) (i : ℕ) :
    complex X i ≅ A.toChainDGAlgebra.natRestriction :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ componentIso X k i) (componentIso_d X i)

/-- The component of the fixed-exponent complex comparison is the canonical term comparison. -/
@[simp]
theorem complexIso_app (X : Even.Extension A d f) (k i : ℕ) :
    HomologicalComplex.Hom.isoApp (complexIso X i) k = componentIso X k i := sorry

/-- The exponent-`i` graded-piece complex is supported in the degrees selected by its
fixed-exponent embedding. -/
instance gradedPieceIsStrictlySupported (X : Even.Extension A d f) (i : ℕ) :
    ((filteredComplex X).gradedPiece (filtrationDegree i)).IsStrictlySupported
      (embedding d i) := sorry

/-- Homology of the fixed-exponent restriction agrees canonically with homology of the full
graded-piece complex in the corresponding total degree. -/
@[stacks 0GZ6 "restriction-to-graded-piece homology comparison"]
def restrictionHomologyIso (X : Even.Extension A d f) (k i : ℕ) :
    (complex X i).homology k ≅
      ((filteredComplex X).gradedPiece (filtrationDegree i)).homology
        (totalDegree d k i) :=
  (HomologicalComplex.homologyMapIso
      (asIso (((filteredComplex X).gradedPiece (filtrationDegree i)).truncLE'ToRestriction
        (embedding d i))) k).symm ≪≫
    ((((filteredComplex X).gradedPiece (filtrationDegree i)).truncLE'
      (embedding d i)).extendHomologyIso
      (embedding d i) (j := k) (j' := totalDegree d k i) rfl).symm ≪≫
    HomologicalComplex.homologyMapIso
      (((filteredComplex X).gradedPiece (filtrationDegree i)).truncLEIso
        (embedding d i)).symm (totalDegree d k i) ≪≫
    HomologicalComplex.homologyMapIso
      (asIso (((filteredComplex X).gradedPiece (filtrationDegree i)).ιTruncLE
        (embedding d i))) (totalDegree d k i)

/-- The cohomology of the exponent-`i` graded piece in total degree `-(k + i * d)` is
canonically isomorphic to `H_k(A)`. -/
@[stacks 0GZ6 "homology of one exponent-graded piece"]
def homologyIso (X : Even.Extension A d f) (k i : ℕ) :
    ((filteredComplex X).gradedPiece (filtrationDegree i)).homology
        (totalDegree d k i) ≅ A.toChainDGAlgebra.homology (k : ℤ) :=
  (restrictionHomologyIso X k i).symm ≪≫
    HomologicalComplex.homologyMapIso (complexIso X i) k ≪≫
    A.toChainDGAlgebra.natRestrictionHomologyIso k

/-- The canonical fixed-exponent homology comparison gives the corresponding
`IsIsomorphic` statement. -/
@[stacks 0GZ6 "fixed-exponent homology isomorphism proposition"]
theorem homology_isIsomorphic (X : Even.Extension A d f) (k i : ℕ) :
    IsIsomorphic
      (((filteredComplex X).gradedPiece (filtrationDegree i)).homology (totalDegree d k i))
      (A.toChainDGAlgebra.homology (k : ℤ)) := sorry

/-- Every spectral sequence associated to the even-cell exponent filtration has first-page
entry `H_k(A)` in the bidegree of `A_k T^[i]`. -/
@[stacks 0GZ6 "associated first-page entry isomorphism proposition"]
theorem associated_isIsomorphic (X : Even.Extension A d f)
    {E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0}
    (hAssoc : FilteredComplex.IsAssociated (filteredComplex X) E) (k i : ℕ) :
    IsIsomorphic ((E.page 1).X (bidegree d k i))
      (A.toChainDGAlgebra.homology (k : ℤ)) := sorry

/-- Compose the association's canonical first-page comparison with the fixed-exponent homology
comparison.  Callers do not choose an entrywise isomorphism. -/
@[stacks 0GZ6 "first-page entry comparison for an even cell"]
def iso (X : Even.Extension A d f)
    {E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0}
    (S : FilteredComplex.Association (filteredComplex X) E) (k i : ℕ) :
    (E.page 1).X (bidegree d k i) ≅ A.toChainDGAlgebra.homology (k : ℤ) :=
  S.pageOneIso (bidegree d k i).1 (bidegree d k i).2 ≪≫
    eqToIso (congrArg
      (fun n : ℤ ↦ ((filteredComplex X).gradedPiece (filtrationDegree i)).homology n)
      ((add_comm (filtrationDegree i)
        (totalDegree d k i - filtrationDegree i)).trans
          (sub_add_cancel (totalDegree d k i) (filtrationDegree i)))) ≪≫
    homologyIso X k i

/-- The fixed-exponent first-page comparison is natural under a morphism of associations over
the identity filtered complex. -/
@[stacks 0GZ6 "naturality of the even-cell first-page comparison"]
theorem iso_naturality (X : Even.Extension A d f)
    {E E' : CohomologicalSpectralSequence (ModuleCat.{v} R) 0}
    {S : FilteredComplex.Association (filteredComplex X) E}
    {T : FilteredComplex.Association (filteredComplex X) E'}
    (phi : FilteredComplex.Association.Hom S T (𝟙 (filteredComplex X))) (k i : ℕ) :
    (phi.hom.hom 1).f (bidegree d k i) ≫ (iso X T k i).hom =
      (iso X S k i).hom := sorry

end Entry

/-! ## Existence, boundedness, and convergence -/

namespace Association

/-- The actual exponent-filtered complex of an even cell admits an associated cohomological
spectral sequence. -/
@[stacks 0GZ6 "existence of an associated even-cell spectral sequence"]
theorem existsAssociated (X : Even.Extension A d f) :
    ∃ E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0,
      FilteredComplex.IsAssociated (filteredComplex X) E := sorry

/-- Every spectral sequence associated to the exponent filtration of an even cell is bounded. -/
@[stacks 0GZ6 "boundedness of an associated even-cell spectral sequence"]
theorem isBounded (X : Even.Extension A d f)
    {E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0}
    (hAssoc : FilteredComplex.IsAssociated (filteredComplex X) E) :
    E.IsBounded := sorry

/-- Every spectral sequence associated to the exponent filtration of an even cell converges to
the cohomology of the filtered complex; `filteredComplexHomologyIso` identifies its negative
degrees with the chain-DGA homology. -/
@[stacks 0GZ6 "convergence of an associated even-cell spectral sequence"]
theorem converges (X : Even.Extension A d f)
    {E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0}
    (hAssoc : FilteredComplex.IsAssociated (filteredComplex X) E) :
    FilteredComplex.Cohomology.Convergence.Converges (filteredComplex X) E := sorry

/-- An even-cell exponent filtration admits an associated spectral sequence which is both
bounded and convergent.  This is an existence statement and does not select sequence data. -/
@[stacks 0GZ6 "bounded convergent even-cell spectral sequence existence"]
theorem existsBoundedConvergent (X : Even.Extension A d f) :
    ∃ E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0,
      FilteredComplex.IsAssociated (filteredComplex X) E ∧ E.IsBounded ∧
        FilteredComplex.Cohomology.Convergence.Converges (filteredComplex X) E := sorry

end Association

/-! ## The attaching-class differential -/

namespace Differential

/-- The attaching element of an even cell, bundled as a cycle in degree `d - 1`. -/
@[stacks 0GZ6 "even-cell attaching cycle"]
def attachingCycle (X : Even.Extension A d f) :
    A.toChainDGAlgebra.cycles ((((d : ℕ) - 1 : ℕ) : ℤ)) :=
  X.toCell.attachingCycle

/-- The homology class of the attaching cycle of an even cell. -/
@[stacks 0GZ6 "even-cell attaching homology class"]
def attachingClass (X : Even.Extension A d f) :
    A.toChainDGAlgebra.homology ((((d : ℕ) - 1 : ℕ) : ℤ)) :=
  A.toChainDGAlgebra.homologyπ _ (attachingCycle X)

/-- Multiplication by the attaching class on base homology. -/
@[stacks 0GZ6 "attaching-class multiplication on homology"]
def attachingClassMul (X : Even.Extension A d f) (k : ℕ) :
    A.toChainDGAlgebra.homology (k : ℤ) →ₗ[R]
      A.toChainDGAlgebra.homology (((((d : ℕ) - 1) + k : ℕ) : ℤ)) :=
  A.toChainDGAlgebra.homologyMul ((d : ℕ) - 1) k (attachingClass X)

/-- Multiplication by the attaching class, regarded as a morphism of canonical homology
modules. -/
@[stacks 0GZ6 "attaching-class homology morphism"]
def attachingClassMulHom (X : Even.Extension A d f) (k : ℕ) :
    A.toChainDGAlgebra.homology (k : ℤ) ⟶
      A.toChainDGAlgebra.homology (((((d : ℕ) - 1) + k : ℕ) : ℤ)) :=
  ModuleCat.ofHom (attachingClassMul X k)

/-- On a represented homology class, multiplication by the attaching class is represented by
chain-level multiplication by the attaching cycle. -/
@[stacks 0GZ6 "attaching-class multiplication on representatives"]
theorem attachingClassMul_homologyπ (X : Even.Extension A d f) (k : ℕ)
    (x : A.toChainDGAlgebra.cycles (k : ℤ)) :
    attachingClassMul X k (A.toChainDGAlgebra.homologyπ k x) =
      A.toChainDGAlgebra.homologyπ ((((d : ℕ) - 1) + k : ℕ) : ℤ)
        (A.toChainDGAlgebra.cyclesMul ((d : ℕ) - 1) k (attachingCycle X) x) := sorry

/-- The exponent-lowering coefficient formula is the chain representative of multiplication by
the attaching class.  This is the explicit bridge from
`coeffDifferential_lowerExponent` to `attachingClassMul_homologyπ`. -/
@[stacks 0GZ6 "lowering differential and attaching-class bridge"]
theorem lowerCoefficient_eq_cyclesMul (X : Even.Extension A d f) (k i : ℕ)
    (x : A.toChainDGAlgebra.cycles (k : ℤ)) :
    lowerProjection A.toChainDGAlgebra.nonnegativePart d k i
        (X.coeffDifferential (lowerSourceDegree d k i)
          (coeffMonomial A.toChainDGAlgebra.nonnegativePart (d : ℕ) k (i + 1)
            (A.toChainDGAlgebra.iCycles k x))) =
      A.toChainDGAlgebra.iCycles ((((d : ℕ) - 1) + k : ℕ) : ℤ)
        (A.toChainDGAlgebra.cyclesMul ((d : ℕ) - 1) k (attachingCycle X) x) := sorry

/-- Under the canonical fixed-exponent comparisons, the actual first differential is
multiplication by the attaching class. -/
@[stacks 0GZ6 "first differential for an even cell"]
theorem square (X : Even.Extension A d f)
    {E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0}
    (S : FilteredComplex.Association (filteredComplex X) E) (k i : ℕ) :
    CommSq
      ((E.page 1).d (bidegree d k (i + 1))
        (bidegree d (((d : ℕ) - 1) + k) i))
      ((Entry.iso X S k (i + 1)).hom)
      ((Entry.iso X S (((d : ℕ) - 1) + k) i).hom)
      (attachingClassMulHom X k) := sorry

end Differential

/-! ## The degree-two Stacks specialization -/

namespace DegreeTwo

variable {f₂ : A.toChainDGAlgebra.nonnegativePiece 1}

/-- For a degree-two cell, multiplication by the attaching class raises homological degree from
`k` to `k + 1`. -/
@[stacks 0GZ6 "degree-two attaching-class target degree"]
theorem targetDegree (k : ℕ) :
    ((((((2 : ℕ+) : ℕ) - 1) + k : ℕ) : ℤ)) = ((k + 1 : ℕ) : ℤ) := sorry

/-- Multiplication by the degree-one attaching class of a degree-two cell, with target written
in the conventional degree `k + 1`. -/
@[stacks 0GZ6 "degree-two attaching-class homology morphism"]
def attachingClassMulHom (X : Even.Extension A (2 : ℕ+) f₂) (k : ℕ) :
    A.toChainDGAlgebra.homology (k : ℤ) ⟶
      A.toChainDGAlgebra.homology ((k + 1 : ℕ) : ℤ) :=
  Differential.attachingClassMulHom X k ≫
    eqToHom (congrArg (fun n : ℤ ↦ A.toChainDGAlgebra.homology n)
      (targetDegree k))

/-- Lemma 23.12.3 (2) (Tag 0GZ6): the degree-two exponent filtration admits an associated
cohomological spectral sequence which is bounded and converges to the cohomology of the cell. -/
@[stacks 0GZ6 "(2), bounded convergent exponent spectral sequence"]
theorem existsBoundedConvergent (X : Even.Extension A (2 : ℕ+) f₂) :
    ∃ E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0,
      FilteredComplex.IsAssociated (filteredComplex X) E ∧ E.IsBounded ∧
        FilteredComplex.Cohomology.Convergence.Converges (filteredComplex X) E := sorry

/-- Lemma 23.12.3 (2) (Tag 0GZ6): in the bidegree occupied by `A_k T^[i]`, the first page of
an associated degree-two exponent spectral sequence is canonically isomorphic to `H_k(A)`. -/
@[stacks 0GZ6 "(2), canonical first-page entry comparison"]
def entryIso (X : Even.Extension A (2 : ℕ+) f₂)
    {E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0}
    (S : FilteredComplex.Association (filteredComplex X) E) (k i : ℕ) :
    (E.page 1).X (bidegree (2 : ℕ+) k i) ≅
      A.toChainDGAlgebra.homology (k : ℤ) :=
  Entry.iso X S k i

/-- Lemma 23.12.3 (2) (Tag 0GZ6): in the bidegree occupied by `A_k T^[i]`, the first page of
every associated degree-two exponent spectral sequence is isomorphic to `H_k(A)`. -/
@[stacks 0GZ6 "(2), first-page entries of the exponent spectral sequence"]
theorem entry_isIsomorphic (X : Even.Extension A (2 : ℕ+) f₂)
    {E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0}
    (hAssoc : FilteredComplex.IsAssociated (filteredComplex X) E) (k i : ℕ) :
    IsIsomorphic ((E.page 1).X (bidegree (2 : ℕ+) k i))
      (A.toChainDGAlgebra.homology (k : ℤ)) := sorry

/-- Lemma 23.12.3 (2) (Tag 0GZ6): under the canonical exponent-wise first-page identifications, the
actual differential from the `T^[i+1]` entry to the `T^[i]` entry is multiplication by the
degree-one attaching class `[f] : H₁(A)`. -/
@[stacks 0GZ6 "(2), first differential induced by the attaching class"]
theorem firstDifferentialSquare (X : Even.Extension A (2 : ℕ+) f₂)
    {E : CohomologicalSpectralSequence (ModuleCat.{v} R) 0}
    (S : FilteredComplex.Association (filteredComplex X) E) (k i : ℕ) :
    CommSq
      ((E.page 1).d (bidegree (2 : ℕ+) k (i + 1))
        (bidegree (2 : ℕ+) (k + 1) i))
      ((entryIso X S k (i + 1)).hom)
      ((entryIso X S (k + 1) i).hom)
      (attachingClassMulHom X k) := sorry

end DegreeTwo

end PageOne
end DividedPowerChainAlgebra.Adjoin.Even.Extension.ExponentFiltration
