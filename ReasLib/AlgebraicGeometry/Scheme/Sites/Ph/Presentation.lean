/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation

/-!
# Chosen presentations of big `ph` sites

The `ph` precoverage consists of presieves represented by `ph` covering
families. A chosen big `ph` site is an explicit small presentation of this
precoverage.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

namespace Scheme

/-- The precoverage on schemes whose covering presieves are represented by
indexed `ph` covering families. -/
def phPrecoverage : Precoverage Scheme.{u} where
  coverings := fun T ↦ {R | ∃ (ι : Type u) (X : ι → Scheme.{u})
    (π : ∀ i, X i ⟶ T), R = Presieve.ofArrows X π ∧ PhCovering X π}

/-- A presieve belongs to the `ph` precoverage exactly when it is represented
by an indexed `ph` covering family. -/
theorem mem_phPrecoverage_iff {T : Scheme.{u}} {R : Presieve T} :
    R ∈ phPrecoverage T ↔
      ∃ (ι : Type u) (X : ι → Scheme.{u}) (π : ∀ i, X i ⟶ T),
        R = Presieve.ofArrows X π ∧ PhCovering X π := sorry

end Scheme

/-- An explicit small presentation of a big `ph` site. -/
abbrev ChosenBigPhSite : Type (max (u + 1) (v + 1)) :=
  ChosenBigSite.{u, v} Scheme.phPrecoverage

end AlgebraicGeometry
