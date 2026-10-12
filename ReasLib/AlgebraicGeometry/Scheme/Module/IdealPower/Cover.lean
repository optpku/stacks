/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Basic

/-!
# Basic-open covers of affine ideal complements

An explicit finite generating family of an ideal determines a cover of
`Spec A ∖ V(I)` by its standard basic opens.  Keeping the family explicit makes
the cover data usable independently of any noncanonical `I.FG` witness.
-/

@[expose] public section

open AlgebraicGeometry PrimeSpectrum
open scoped AlgebraicGeometry

universe u

namespace Ideal.FiniteGeneratingFamily

variable {A : Type u} [CommRing A]
variable {I : Ideal A}

/-- The basic open of `Spec A` attached to a member of a finite generating family. -/
def basicOpen (G : I.FiniteGeneratingFamily) (i : G.Index) :
    (Spec (.of A)).Opens :=
  PrimeSpectrum.basicOpen (G.generator i)

/-- Each basic open from a finite generating family lies in `Spec A ∖ V(I)`. -/
theorem basicOpen_le_idealComplementOpens (G : I.FiniteGeneratingFamily) (i : G.Index) :
    G.basicOpen i ≤ AlgebraicGeometry.Scheme.Modules.idealComplementOpens I := sorry

/-- The basic opens attached to a finite generating family cover `Spec A ∖ V(I)`. -/
theorem idealComplementOpens_le_iSup_basicOpen (G : I.FiniteGeneratingFamily) :
    AlgebraicGeometry.Scheme.Modules.idealComplementOpens I ≤ iSup G.basicOpen := sorry

end Ideal.FiniteGeneratingFamily

