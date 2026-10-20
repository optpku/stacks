module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import stacks_project.Chap07.Definition_7_6_2_Site
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiSite

/-!
# Small Zariski site of an algebraic space

The small Zariski site of an algebraic space `F` is the category of open subspaces of
`F`, with covering families the Zariski coverings of those open subspaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The Zariski covering families on open subspaces of an algebraic space satisfy the site
axioms. -/
instance smallZariskiPrecoverage.instIsSite {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (smallZariskiPrecoverage F).IsSite := by
  let h := smallZariskiPrecoverage_site_axioms F
  exact @Precoverage.IsSite.mk _ _ (smallZariskiPrecoverage F)
    h.1 h.2.1 ⟨h.2.2.1⟩ ⟨h.2.2.2⟩

end AlgebraicGeometry.AlgebraicSpace
