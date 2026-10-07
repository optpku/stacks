module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Determinant.Exact
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u}}

/- Lemma 17.26.1 (0B38): for a short exact sequence
`0 ⟶ E₁ ⟶ E₂ ⟶ E₃ ⟶ 0` of finite locally free `𝒪_X`-modules, the source
asserts a canonical isomorphism `det(E₁) ⊗ det(E₃) ≅ det(E₂)`.

The intrinsic determinant, its inclusion into `Λ(E)`, and its kernel universal property are the
shared `RingedSpace.Determinant` API recalled below.  On every fixed-rank piece, `topIso` identifies
this annihilator owner with the top exterior power.  The shared `Determinant.Exact` API now
characterizes the short-exact comparison by its local split formula, proves choice-free existence
and uniqueness, and records invertibility.  This source-facing file still displays the bundled
isomorphism required by the source rather than manufacturing that non-Prop datum from a provisional
existence proof. -/

#check @Determinant.action
#check @Determinant.subobject
#check @Determinant.sheaf
#check @Determinant.ι
#check @Determinant.factors_iff
#check @Determinant.lift
#check @Determinant.lift_ι
#check @Determinant.mapIso
#check @Determinant.mapIso_hom_ι
#check fun (F : X.Modules) (r : ℕ) [IsFiniteLocallyFreeOfRank r F] ↦
  (RingedSite.Determinant.topIso X.sheaf F r :
    Determinant.sheaf F ≅ ExteriorPower.sheaf F r)
#check fun (F : X.Modules) (r : ℕ) [IsFiniteLocallyFreeOfRank r F] ↦
  RingedSite.Determinant.topIso_hom_powerι X.sheaf F r
#check @Determinant.Exact.IsFormula
#check @Determinant.Exact.IsComparison
#check @Determinant.Exact.comparison_unique
#check @Determinant.Exact.existsUnique_comparison
#check @Determinant.Exact.IsFormula.isIso_restriction
#check @Determinant.Exact.comparison_isIso
#check @Determinant.Exact.existsUnique_comparison_isIso
#check @Determinant.Exact.existsUnique_comparisonIso

section StatementShape

variable {S : ShortComplex X.Modules}

/- Lemma 17.26.1 (0B38): the local determinant formula uniquely characterizes a bundled
isomorphism.  The source's three finite-locally-free assumptions are explicit here, while the
shared theorem records the stronger fact that only the endpoints are needed. -/
@[stacks 0B38]
#check fun (hS : S.ShortExact)
    [S.X₁.IsFiniteLocallyFree]
    [S.X₂.IsFiniteLocallyFree]
    [S.X₃.IsFiniteLocallyFree] ↦
  Determinant.Exact.existsUnique_comparisonIso hS

/- The shared theorem is more general on invertibility: the local splitting argument only needs
the two endpoint modules to be finite locally free. -/
#check @Determinant.Exact.existsUnique_comparison_isIso

end StatementShape

end AlgebraicGeometry.RingedSpace
