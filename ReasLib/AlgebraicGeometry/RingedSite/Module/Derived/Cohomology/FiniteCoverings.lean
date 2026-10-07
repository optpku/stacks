module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology.Dimension
public import ReasLib.CategoryTheory.Sites.Cech.Cofinal.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology and finite cofinal covering systems

A finite cofinal Cech system makes module cohomology over every controlled object commute with
arbitrary coproducts.  The covering data are coefficient-independent; this leaf supplies the
ringed-site module specialization consumed by relative compactness results.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf.Cech.CofinalSystem

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleCohomology

variable (X : RingedSite.{u, v, w}) [UnivLE.{max u v, w}]
variable [∀ U : X, HasFiniteProducts (Over U)]
variable [HasSheafify X.siteTopology AddCommGrpCat.{w}]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat.{w})]
variable [IsGrothendieckAbelian.{w} (RingedSite.ModuleCat.{w} X)]

/-- Lemma 21.52.4 (0G22): a finite cofinal covering system makes every module-cohomology
functor over an object in the controlled family preserve coproducts. -/
@[stacks 0G22 "cohomology coproducts from finite cofinal coverings"]
theorem preservesCoproducts_of_finiteCoverings
    (B : Set X)
    (Cov : ∀ U : X, Set (FormalCoproduct (Over U)))
    (hCov : FiniteCoverings X.siteTopology B Cov)
    {U : X} (hU : U ∈ B) :
    PreservesCoproducts X U := sorry

end RingedSite.Hom.ModuleCohomology

end
