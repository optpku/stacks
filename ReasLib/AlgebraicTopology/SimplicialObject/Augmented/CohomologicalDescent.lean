module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

/-!
# Cohomological descent for augmented simplicial spaces

This leaf owns the degreewise pullback and sheaf-cohomology objects attached to any augmented
simplicial topological space.  Neither total cohomology nor a coefficient-functorial spectral
sequence for simplicial topological spaces is yet constructed in Mathlib or ReasLib, so descent
and convergence are properties rather than fields of a placeholder data package.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject.Augmented

variable (A : SimplicialObject.Augmented TopCat.{u})

/-- Pull an abelian sheaf on the augmentation point back to degree `p` of an augmented
simplicial topological space. -/
@[stacks 02N9 "degreewise pullback on an augmented simplicial space"]
abbrev pullbackSheaf
    (ℱ : A.right.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    (A.left _⦋p⦌).Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pullback AddCommGrpCat
    (A.hom.app (op <| SimplexCategory.mk p))).obj ℱ

/-- Degreewise sheaf cohomology `H^q(U_p, ε_p^*ℱ)` of an augmented simplicial
topological space. -/
@[stacks 02N9 "degreewise pullback cohomology"]
abbrev degreeCohomology
    (ℱ : A.right.Sheaf AddCommGrpCat.{u}) (p q : ℕ) : AddCommGrpCat.{u} :=
  (A.pullbackSheaf ℱ p).H' q (⊤ : Opens (A.left _⦋p⦌))

section BaseCohomology

/-- A proposed total cohomology theory for the pulled-back sheaf satisfies cohomological descent
when it is degreewise isomorphic to sheaf cohomology at the augmentation point.  The explicit
`totalCohomology` argument is the boundary for a future canonical construction of
`H^n(U_•, ε^*ℱ)`. -/
@[stacks 02N9 "cohomological descent predicate"]
def IsCohomologicalDescent
    (ℱ : A.right.Sheaf AddCommGrpCat.{u})
    (totalCohomology : ℕ → AddCommGrpCat.{u}) : Prop :=
  ∀ n : ℕ, IsIsomorphic (totalCohomology n) (ℱ.H' n (⊤ : Opens A.right))

namespace IsCohomologicalDescent

/-- Cohomological descent identifies a specified total-cohomology object with cohomology at the
augmentation point in every degree. -/
theorem isIsomorphic
    {ℱ : A.right.Sheaf AddCommGrpCat.{u}}
    {totalCohomology : ℕ → AddCommGrpCat.{u}}
    (h : A.IsCohomologicalDescent ℱ totalCohomology) (n : ℕ) :
    IsIsomorphic (totalCohomology n) (ℱ.H' n (⊤ : Opens A.right)) := sorry

/-- If a spectral sequence abuts to a proposed total cohomology satisfying descent, then it
abuts to sheaf cohomology at the augmentation point. -/
theorem abutsTo
    {ℱ : A.right.Sheaf AddCommGrpCat.{u}}
    {totalCohomology : ℕ → AddCommGrpCat.{u}}
    {E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u} 1}
    (h : A.IsCohomologicalDescent ℱ totalCohomology)
    (hE : CohomologicalSpectralSequenceNat.AbutsTo E totalCohomology) :
    CohomologicalSpectralSequenceNat.AbutsTo E
      (fun n ↦ ℱ.H' n (⊤ : Opens A.right)) := sorry

end IsCohomologicalDescent

end BaseCohomology

section PageOne

/-- A first-quadrant cohomological spectral sequence has the degreewise pullback cohomology
`H^q(U_p, ε_p^*ℱ)` of an augmented simplicial space as its `E₁` page. -/
@[stacks 02N9 "augmented-simplicial-space E1 page"]
def IsPageOne
    (ℱ : A.right.Sheaf AddCommGrpCat.{u})
    (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u} 1) : Prop :=
  ∀ p q : ℕ,
    IsIsomorphic ((E.page 1).X (p, q)) (A.degreeCohomology ℱ p q)

namespace IsPageOne

/-- The page-one property gives the degreewise pullback-cohomology identification at `(p, q)`. -/
theorem isIsomorphic
    {ℱ : A.right.Sheaf AddCommGrpCat.{u}}
    {E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u} 1}
    (h : A.IsPageOne ℱ E) (p q : ℕ) :
    IsIsomorphic ((E.page 1).X (p, q)) (A.degreeCohomology ℱ p q) := sorry

end IsPageOne

end PageOne

section DescentSpectralSequence

/-- A descent spectral sequence for an augmented simplicial space has degreewise pullback
cohomology as its `E₁` page and, after cohomological descent, abuts directly to sheaf
cohomology at the augmentation point. -/
@[stacks 02N9 "augmented-simplicial-space descent spectral sequence predicate"]
def IsDescentSpectralSequence
    (ℱ : A.right.Sheaf AddCommGrpCat.{u})
    (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u} 1) : Prop :=
  A.IsPageOne ℱ E ∧
    CohomologicalSpectralSequenceNat.AbutsTo E
      (fun n ↦ ℱ.H' n (⊤ : Opens A.right))

namespace IsDescentSpectralSequence

variable {ℱ : A.right.Sheaf AddCommGrpCat.{u}}
variable {E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u} 1}

/-- A descent spectral sequence has the required degreewise pullback-cohomology `E₁` page. -/
theorem pageOne (h : A.IsDescentSpectralSequence ℱ E) :
    A.IsPageOne ℱ E := sorry

/-- A descent spectral sequence abuts directly to sheaf cohomology at the augmentation point. -/
theorem abutsTo (h : A.IsDescentSpectralSequence ℱ E) :
    CohomologicalSpectralSequenceNat.AbutsTo E
      (fun n ↦ ℱ.H' n (⊤ : Opens A.right)) := sorry

/-- Assemble a descent spectral sequence from its page-one identification and direct
base-cohomology abutment. -/
theorem of
    (hPageOne : A.IsPageOne ℱ E)
    (hAbutsTo : CohomologicalSpectralSequenceNat.AbutsTo E
      (fun n ↦ ℱ.H' n (⊤ : Opens A.right))) :
    A.IsDescentSpectralSequence ℱ E := sorry

/-- Assemble a descent spectral sequence from an abutment to a proposed total cohomology and a
cohomological-descent comparison for that total cohomology. -/
theorem of_total
    (hPageOne : A.IsPageOne ℱ E)
    {totalCohomology : ℕ → AddCommGrpCat.{u}}
    (hAbutsTo : CohomologicalSpectralSequenceNat.AbutsTo E totalCohomology)
    (hDescent : A.IsCohomologicalDescent ℱ totalCohomology) :
    A.IsDescentSpectralSequence ℱ E := sorry

end IsDescentSpectralSequence

end DescentSpectralSequence

end CategoryTheory.SimplicialObject.Augmented
