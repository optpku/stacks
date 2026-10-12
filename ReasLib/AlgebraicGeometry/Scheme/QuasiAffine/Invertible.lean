/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IsQuasiAffine

/-- On a quasi-affine scheme, every finite subset of an open is contained in an affine
nonvanishing open of a global section of any invertible module, itself contained in that open. -/
theorem exists_affineSectionNonvanishingOpen_between
    {X : Scheme.{u}} [X.IsQuasiAffine] {L : X.Modules}
    [hL : Scheme.Modules.Invertible L]
    (E : Set X) (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ s : Γ(L, ⊤),
      IsAffineOpen (hL.sectionNonvanishingOpen s) ∧
        E ⊆ (hL.sectionNonvanishingOpen s : Set X) ∧
          hL.sectionNonvanishingOpen s ≤ W := sorry

end AlgebraicGeometry.Scheme.IsQuasiAffine
