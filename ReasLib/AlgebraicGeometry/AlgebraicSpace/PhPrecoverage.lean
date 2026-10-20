/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Ph
public import ReasLib.CategoryTheory.Sites.PrecoverageSite

/-!
# The ph precoverage on algebraic spaces

Covering presieves are represented by indexed ph covering families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The ph precoverage on algebraic spaces over `S`: covering presieves are those
represented by an indexed ph covering family. -/
def phPrecoverage : Precoverage (AlgebraicSpace S) where
  coverings X :=
    {R | ∃ (ι : Type (u + 1)) (Y : ι → AlgebraicSpace S) (f : ∀ i, Y i ⟶ X),
      R = Presieve.ofArrows Y f ∧ PhCovering Y f}

/-- A presieve belongs to `phPrecoverage` if and only if it is represented by an
indexed ph covering family. -/
theorem mem_phPrecoverage_iff {X : AlgebraicSpace S} {R : Presieve X} :
    R ∈ phPrecoverage X ↔
      ∃ (ι : Type (u + 1)) (Y : ι → AlgebraicSpace S) (f : ∀ i, Y i ⟶ X),
        R = Presieve.ofArrows Y f ∧ PhCovering Y f :=
  sorry

/-- An indexed family belongs to `phPrecoverage` if and only if it is a ph
covering. -/
theorem ofArrows_mem_phPrecoverage_iff {X : AlgebraicSpace S}
    {ι : Type (u + 1)} {Y : ι → AlgebraicSpace S} (f : ∀ i, Y i ⟶ X) :
    Presieve.ofArrows Y f ∈ phPrecoverage X ↔ PhCovering Y f :=
  sorry

/-- The ph covering class of algebraic spaces over `S` satisfies the site
axioms. -/
instance phPrecoverage.instIsSite :
    (phPrecoverage : Precoverage (AlgebraicSpace S)).IsSite :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
