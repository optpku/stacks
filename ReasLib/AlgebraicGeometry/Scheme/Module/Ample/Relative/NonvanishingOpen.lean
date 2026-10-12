/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen

/-!
# Nonvanishing opens of relatively ample modules

The nonvanishing open of a section of a relatively ample module is affine over a
universally closed base morphism.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- For a universally closed morphism, the nonvanishing open of a global section of a
relatively ample module is affine over the base. -/
theorem RelativelyAmple.isAffineHom_sectionNonvanishingOpen
    {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
    [h : RelativelyAmple f L] [UniversallyClosed f]
    (s : Γ(L, ⊤)) :
    IsAffineHom ((h.invertible.sectionNonvanishingOpen s).ι ≫ f) := sorry

end AlgebraicGeometry
