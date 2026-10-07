module

public import Mathlib.AlgebraicTopology.DoldKan.Normalized
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The normalized Moore projection

This module packages Mathlib's objectwise projector onto the normalized Moore complex as a
natural transformation. It is the variance-dual companion to `inclusionOfMooreComplex`.

@stack 019A
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace AlgebraicTopology

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The natural projection from alternating-face complexes to normalized Moore complexes. -/
@[stacks 019A "normalized Moore projection natural transformation"]
def projectionToMooreComplex (A : Type u) [Category.{v} A] [Abelian A] :
    alternatingFaceMapComplex A ⟶ normalizedMooreComplex A where
  app := DoldKan.PInftyToNormalizedMooreComplex
  naturality _ _ f := DoldKan.PInftyToNormalizedMooreComplex_naturality f

/-- The component of the normalized Moore projection at a simplicial object. -/
@[simp, stacks 019A "normalized Moore projection component"]
theorem projectionToMooreComplex_app (U : SimplicialObject A) :
    (projectionToMooreComplex A).app U = DoldKan.PInftyToNormalizedMooreComplex U := sorry

namespace normalizedMooreComplex

/-- The normalized Moore inclusion followed by the canonical projection is the identity. -/
@[reassoc, stacks 019A "normalized Moore retract law"]
theorem inclusion_comp_projection (A : Type u) [Category.{v} A] [Abelian A] :
    inclusionOfMooreComplex A ≫ projectionToMooreComplex A =
      𝟙 (normalizedMooreComplex A) := sorry

namespace inclusion

/-- The normalized Moore inclusion, equipped with its natural retraction. -/
@[stacks 019A "normalized Moore split monomorphism"]
def splitMono (A : Type u) [Category.{v} A] [Abelian A] :
    SplitMono (inclusionOfMooreComplex A) where
  retraction := projectionToMooreComplex A
  id := normalizedMooreComplex.inclusion_comp_projection A

/-- The componentwise normalized Moore inclusion, equipped with its canonical retraction. -/
@[stacks 019A "normalized Moore component split monomorphism"]
def appSplitMono (U : SimplicialObject A) : SplitMono (inclusionOfMooreComplexMap U) :=
  DoldKan.splitMonoInclusionOfMooreComplexMap U

/-- The normalized Moore inclusion is canonically split as a natural transformation. -/
@[stacks 019A "normalized Moore split monomorphism instance"]
instance isSplitMono (A : Type u) [Category.{v} A] [Abelian A] :
    IsSplitMono (inclusionOfMooreComplex A) := sorry

/-- Every component of the normalized Moore inclusion is canonically split. -/
@[stacks 019A "normalized Moore component split monomorphism instance"]
instance appIsSplitMono (U : SimplicialObject A) :
    IsSplitMono (inclusionOfMooreComplexMap U) := sorry

end inclusion

namespace projection

/-- The normalized Moore projection, equipped with its natural section. -/
@[stacks 019A "normalized Moore split epimorphism"]
def splitEpi (A : Type u) [Category.{v} A] [Abelian A] :
    SplitEpi (projectionToMooreComplex A) where
  section_ := inclusionOfMooreComplex A
  id := normalizedMooreComplex.inclusion_comp_projection A

/-- The componentwise normalized Moore projection, equipped with its canonical section. -/
@[stacks 019A "normalized Moore component split epimorphism"]
def appSplitEpi (U : SimplicialObject A) :
    SplitEpi (DoldKan.PInftyToNormalizedMooreComplex U) where
  section_ := inclusionOfMooreComplexMap U
  id := (inclusion.appSplitMono U).id

/-- The normalized Moore projection is canonically split as a natural transformation. -/
@[stacks 019A "normalized Moore split epimorphism instance"]
instance isSplitEpi (A : Type u) [Category.{v} A] [Abelian A] :
    IsSplitEpi (projectionToMooreComplex A) := sorry

/-- Every component of the normalized Moore projection is canonically split. -/
@[stacks 019A "normalized Moore component split epimorphism instance"]
instance appIsSplitEpi (U : SimplicialObject A) :
    IsSplitEpi (DoldKan.PInftyToNormalizedMooreComplex U) := sorry

end projection

end normalizedMooreComplex

end AlgebraicTopology
