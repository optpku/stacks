/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A bound for the cohomological dimension of a quasi-compact and
quasi-separated scheme, expressed by vanishing of étale sheaf cohomology for
locally torsion abelian sheaves on the small étale site. -/
def cohomologicalDimensionBound (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (n : WithTop ℕ)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] : Prop :=
  ∀ (i : ℕ), n < (i : WithTop ℕ) →
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
      Sheaf.IsLocallyTorsion F →
        IsZero ((Sheaf.functorH X.smallEtaleTopology i).obj F)

/-- The cohomological dimension of a quasi-compact and quasi-separated scheme
is the least `n : WithTop ℕ` such that every locally torsion abelian sheaf on
its small étale site has vanishing cohomology in degrees strictly above `n`. -/
def cohomologicalDimension (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] : WithTop ℕ :=
  sInf {n : WithTop ℕ | cohomologicalDimensionBound X n}

/-- The scheme-level cohomological dimension satisfies its defining vanishing bound. -/
theorem cohomologicalDimension_isBound (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    cohomologicalDimensionBound X (cohomologicalDimension X) := sorry

/-- Every admissible vanishing bound is at least the scheme-level cohomological dimension. -/
theorem cohomologicalDimension_le_of_bound (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (n : WithTop ℕ)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (hn : cohomologicalDimensionBound X n) :
    cohomologicalDimension X ≤ n := sorry

end AlgebraicGeometry.Scheme

end
