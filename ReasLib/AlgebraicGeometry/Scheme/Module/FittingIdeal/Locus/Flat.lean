module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Locus.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Locus.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.TFAE

/-!
# The flat locus of a scheme module

The coproduct of the successive Fitting rank loci represents the locus where a finitely
presented module is flat.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The coproduct of all successive Fitting rank loci of a scheme module. -/
noncomputable abbrev fittingFlatLocus
    {S : Scheme.{u}} (F : S.Modules) : Scheme :=
  ∐ fun r : ℕ ↦ fittingRankLocus F r

/-- The canonical morphism from the coproduct of the Fitting rank loci to the ambient scheme. -/
noncomputable abbrev fittingFlatLocusι
    {S : Scheme.{u}} (F : S.Modules) : fittingFlatLocus F ⟶ S :=
  Sigma.desc fun r : ℕ ↦ fittingRankLocusι F r

/-- Pulling a finitely presented module back to its `r`th Fitting rank locus gives a finite
locally free module of rank `r`. -/
theorem fittingRankLocus_pullback_isFiniteLocallyFreeOfRank
    {S : Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation] (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Modules.pullback (fittingRankLocusι F r)).obj F) := sorry

/-- The coproduct of the Fitting rank loci represents the locus where the pullback of a
finitely presented module is flat. -/
theorem fittingFlatLocus_nonempty_over_hom_iff_isFlat
    {S T : Scheme.{u}} (g : T ⟶ S) (F : S.Modules) [F.IsFinitePresentation] :
    Subsingleton (Over.mk g ⟶ Over.mk (fittingFlatLocusι F)) ∧
      (Nonempty (Over.mk g ⟶ Over.mk (fittingFlatLocusι F)) ↔
        SheafOfModules.IsFlat ((Modules.pullback g).obj F)) := sorry

/-- The morphism from the flat locus of a finitely presented module to the ambient scheme is
of finite presentation. -/
theorem fittingFlatLocus_hom_finitePresentation
    {S : Scheme.{u}} (F : S.Modules) [F.IsFinitePresentation] :
    Hom.FinitePresentation (fittingFlatLocusι F) := sorry

end AlgebraicGeometry.Scheme
