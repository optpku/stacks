/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.BigQuasicoherent

/-!
# Internal Hom from finite locally free associated modules

This module records the canonical comparison between scheme-level internal Hom
and internal Hom on a big standard site when the source is finite locally free.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- For a finite locally free source, the canonical comparison from the
associated scheme-level internal Hom to internal Hom on a big standard site is
invertible. -/
instance bigModuleInternalHomComparisonIsIsoOfFiniteLocallyFree
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S)
    [F.obj.IsFiniteLocallyFree] :
    IsIso (bigModuleInternalHomComparison S τ F G
      (inferInstance : F.obj.IsFinitePresentation)) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
