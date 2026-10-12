/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable
public import ReasLib.Algebra.Homology.HomologicalComplex.ShortExact.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Horseshoes for Property-Indexed Bounded-Below Resolutions

This file owns the property-neutral data of a horseshoe for variable-lower-bound right
resolutions.  A horseshoe retains a prescribed resolution of the left term, chooses a resolution
of the right term, and records a short exact resolving row together with its comparison from the
source row.  Existence requires additional hypotheses on the object property and belongs in
specialized modules.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.Plus.TermsIn.QuasiIsoTo

variable {A : Type u} [Category.{v} A] [Abelian A]
  {P : ObjectProperty A}

/-- A property-indexed bounded-below horseshoe extending a prescribed right resolution of the
left term of a short complex.  Both the source row and the underlying resolving row are short
exact. -/
@[stacks 013T "property-indexed bounded-below horseshoe"]
structure Horseshoe (S : ShortComplex (CochainComplex A ℤ))
    (R : QuasiIsoTo P S.X₁) where
  /-- The source row is short exact. -/
  sourceShortExact : S.ShortExact
  /-- The chosen property-indexed bounded-below resolution of the right term. -/
  rightResolution : QuasiIsoTo P S.X₃
  /-- The middle bounded-below complex whose terms satisfy `P`. -/
  middle : Plus.TermsIn P
  /-- The left arrow of the resolving row. -/
  f : R.model ⟶ middle
  /-- The right arrow of the resolving row. -/
  g : middle ⟶ rightResolution.model
  /-- The two arrows of the resolving row have zero composite. -/
  zero : f ≫ g = 0
  /-- The comparison from the source row to the underlying resolving row. -/
  comparison : S ⟶
    (ShortComplex.mk f g zero).map (Plus.TermsIn.ι P)
  /-- The left component is the comparison of the prescribed resolution. -/
  comparison_left : comparison.τ₁ = R.comparison
  /-- The right component is the comparison of the chosen right resolution. -/
  comparison_right : comparison.τ₃ = rightResolution.comparison
  /-- The underlying resolving row is short exact. -/
  shortExact :
    ((ShortComplex.mk f g zero).map (Plus.TermsIn.ι P)).ShortExact

attribute [simp] Horseshoe.comparison_left Horseshoe.comparison_right

namespace Horseshoe

variable {S : ShortComplex (CochainComplex A ℤ)}
  {R : QuasiIsoTo P S.X₁}

/-- The resolving row of bounded-below termwise-`P` complexes in a horseshoe. -/
abbrev row (H : Horseshoe S R) : ShortComplex (Plus.TermsIn P) :=
  ShortComplex.mk H.f H.g H.zero

/-- The named resolving row remains short exact after forgetting to cochain complexes. -/
theorem row_shortExact (H : Horseshoe S R) :
    (H.row.map (Plus.TermsIn.ι P)).ShortExact := sorry

/-- The degree-`n` short complex underlying the resolving row. -/
abbrev rowEval (H : Horseshoe S R) (n : ℤ) : ShortComplex A :=
  (H.row.map (Plus.TermsIn.ι P)).map
    (HomologicalComplex.eval A (ComplexShape.up ℤ) n)

/-- The degree-`n` resolving row is short exact. -/
theorem rowEval_shortExact (H : Horseshoe S R) (n : ℤ) :
    (H.rowEval n).ShortExact := sorry

/-- The left object of the resolving row is the prescribed model. -/
@[simp]
theorem row_X₁ (H : Horseshoe S R) : H.row.X₁ = R.model := sorry

/-- The middle object of the resolving row is the horseshoe middle model. -/
@[simp]
theorem row_X₂ (H : Horseshoe S R) : H.row.X₂ = H.middle := sorry

/-- The right object of the resolving row is the chosen right model. -/
@[simp]
theorem row_X₃ (H : Horseshoe S R) : H.row.X₃ = H.rightResolution.model := sorry

/-- The left arrow of the resolving row is the horseshoe left model morphism. -/
@[simp]
theorem row_f (H : Horseshoe S R) : H.row.f = H.f := sorry

/-- The right arrow of the resolving row is the horseshoe right model morphism. -/
@[simp]
theorem row_g (H : Horseshoe S R) : H.row.g = H.g := sorry

/-- The comparison from the source row to the resolving row, expressed through `row`. -/
abbrev rowComparison (H : Horseshoe S R) : S ⟶ H.row.map (Plus.TermsIn.ι P) :=
  H.comparison

/-- The middle component of the comparison carried by a property-indexed horseshoe. -/
abbrev middleComparison (H : Horseshoe S R) : S.X₂ ⟶ H.middle :=
  H.comparison.τ₂

/-- The left component of the row comparison is the prescribed resolution comparison. -/
@[simp]
theorem rowComparison_τ₁ (H : Horseshoe S R) :
    H.rowComparison.τ₁ = R.comparison := sorry

/-- The middle component of the row comparison is the horseshoe middle comparison. -/
@[simp]
theorem rowComparison_τ₂ (H : Horseshoe S R) :
    H.rowComparison.τ₂ = H.middleComparison := sorry

/-- The right component of the row comparison is the chosen right-resolution comparison. -/
@[simp]
theorem rowComparison_τ₃ (H : Horseshoe S R) :
    H.rowComparison.τ₃ = H.rightResolution.comparison := sorry

/-- The left component of a property-indexed horseshoe comparison is a quasi-isomorphism. -/
theorem leftComparison_quasiIso (H : Horseshoe S R) :
    QuasiIso H.comparison.τ₁ := sorry

/-- The right component of a property-indexed horseshoe comparison is a quasi-isomorphism. -/
theorem rightComparison_quasiIso (H : Horseshoe S R) :
    QuasiIso H.comparison.τ₃ := sorry

/-- The middle component of a property-indexed horseshoe comparison is a quasi-isomorphism. -/
theorem middleComparison_quasiIso (H : Horseshoe S R) :
    QuasiIso H.middleComparison := sorry

/-- The property-indexed bounded-below resolution of the middle term supplied by a horseshoe. -/
@[stacks 013T "middle resolution of a property-indexed bounded-below horseshoe"]
def middleResolution (H : Horseshoe S R) : QuasiIsoTo P S.X₂ :=
  QuasiIsoTo.mk H.middle H.middleComparison H.middleComparison_quasiIso

/-- The bundled model of the middle resolution is the horseshoe middle object. -/
@[simp]
theorem middleResolution_model (H : Horseshoe S R) :
    H.middleResolution.model = H.middle := sorry

/-- The underlying complex of the middle resolution is the horseshoe middle complex. -/
@[simp]
theorem middleResolution_complex (H : Horseshoe S R) :
    H.middleResolution.complex = (H.middle : CochainComplex A ℤ) := sorry

/-- The comparison of the middle resolution is the middle comparison of the horseshoe. -/
@[simp]
theorem middleResolution_comparison (H : Horseshoe S R) :
    H.middleResolution.comparison = H.middleComparison := sorry


end Horseshoe


end CochainComplex.Plus.TermsIn.QuasiIsoTo
