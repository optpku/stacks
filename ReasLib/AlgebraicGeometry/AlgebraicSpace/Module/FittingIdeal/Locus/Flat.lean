/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal.Locus.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemePullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat

/-!
# The flat locus of a module on an algebraic space

The coproduct of the successive Fitting rank loci represents the locus where a
finitely presented module is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The coproduct of all successive Fitting rank loci of a module on an
algebraic space. -/
noncomputable abbrev fittingFlatLocus {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] : AlgebraicSpace S :=
  coproduct fun r : ℕ ↦ (fittingRankLocus F r).X

/-- The canonical morphism from the coproduct of the Fitting rank loci to the
ambient algebraic space. -/
noncomputable abbrev fittingFlatLocusι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    fittingFlatLocus F ⟶ X :=
  coproductDesc fun r : ℕ ↦ (fittingRankLocus F r).ι

/-- Postcomposing a rank-locus inclusion with the structure map of the Fitting
flat locus recovers the rank-locus immersion. -/
theorem fittingRankLocus_ι_comp_fittingFlatLocusι {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) :
    coproductι (fun n : ℕ ↦ (fittingRankLocus F n).X) r ≫ fittingFlatLocusι F =
      (fittingRankLocus F r).ι :=
  coproductι_desc (fun n : ℕ ↦ (fittingRankLocus F n).ι) r

/-- The coproduct of the Fitting rank loci represents the functor on schemes
over an algebraic space that is a singleton exactly when the pullback of a
finitely presented module is flat. -/
theorem fittingFlatLocus_nonempty_over_hom_iff_isFlat
    {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (g : ofOver T ⟶ X) (F : X.Modules) [F.IsFinitePresentation] :
    Subsingleton (Over.mk g ⟶ Over.mk (fittingFlatLocusι F)) ∧
      (Nonempty (Over.mk g ⟶ Over.mk (fittingFlatLocusι F)) ↔
        SheafOfModules.IsFlat (Modules.pullbackToScheme g F)) :=
  sorry

/-- The restriction of a finitely presented module to its rank-`r` Fitting
locus is finite locally free of rank `r`. -/
instance fittingRankLocus_pullback_isFiniteLocallyFreeOfRank
    {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFinitePresentation] (r : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank r
      ((Modules.pullback (fittingRankLocus F r).ι).obj F) :=
  sorry

/-- The structure morphism from the coproduct of the Fitting rank loci of a
finitely presented module to the ambient algebraic space is of finite presentation. -/
instance fittingFlatLocus_finitePresentation {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsFinitePresentation] :
    FinitePresentation (fittingFlatLocusι F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
