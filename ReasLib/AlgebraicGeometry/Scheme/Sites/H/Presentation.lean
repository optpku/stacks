/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Stability
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation
public import ReasLib.CategoryTheory.Sites.PrecoverageStability

/-!
# Chosen presentations of big h sites

The h precoverage consists of presieves represented by h covering families.
A chosen big h site is an explicit small presentation of this precoverage.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

namespace Scheme

/-- The precoverage on schemes whose covering presieves are represented by
indexed h covering families. -/
def hPrecoverage : Precoverage Scheme.{u} where
  coverings := fun T ↦ {R | ∃ (ι : Type u) (X : ι → Over T),
    R = Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∧ HCovering X}

/-- A presieve belongs to the h precoverage exactly when it is represented by
an indexed h covering family. -/
theorem mem_hPrecoverage_iff {T : Scheme.{u}} {R : Presieve T} :
    R ∈ hPrecoverage T ↔
      ∃ (ι : Type u) (X : ι → Over T),
        R = Presieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∧ HCovering X := sorry

/-- The h precoverage contains the singleton family induced by every isomorphism. -/
instance hPrecoverageHasIsos : Precoverage.HasIsos hPrecoverage := sorry

/-- The h precoverage is stable under dependent composition of covering families. -/
instance hPrecoverageIsStableUnderBind :
    Precoverage.IsStableUnderBind hPrecoverage := sorry

/-- Pullbacks of h covering families have h covering factoring refinements. -/
instance hPrecoverageHasFactoringPullbacks :
    Precoverage.HasFactoringPullbacks hPrecoverage := sorry

end Scheme

/-- An explicit small presentation of a big h site. -/
abbrev ChosenBigHSite : Type (max (u + 1) (v + 1)) :=
  ChosenBigSite.{u, v} Scheme.hPrecoverage

end AlgebraicGeometry
