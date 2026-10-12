/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement.Resolution.Variable
public import ReasLib.Algebra.Homology.HomologicalComplex.ShortExact.QuasiIso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Horseshoes for Property-Indexed Bounded-Above Resolutions

This file owns the property-neutral data of a horseshoe for variable-upper-bound left
resolutions.  A horseshoe chooses a resolution of the left term, retains a prescribed resolution
of the right term, and records a short exact resolving row together with its comparison to the
source row.  Existence requires additional hypotheses on the object property and belongs in
specialized modules.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.Minus.TermsIn.QuasiIsoFrom

variable {A : Type u} [Category.{v} A] [Abelian A]
  {P : ObjectProperty A}

/-- A property-indexed bounded-above horseshoe extending a prescribed left resolution of the
right term of a short complex.  Both the source row and the underlying resolving row are short
exact. -/
@[stacks 064C "property-indexed bounded-above horseshoe"]
structure Horseshoe (S : ShortComplex (CochainComplex A ℤ))
    (R : QuasiIsoFrom P S.X₃) where
  /-- The source row is short exact. -/
  sourceShortExact : S.ShortExact
  /-- The chosen property-indexed bounded-above resolution of the left term. -/
  leftResolution : QuasiIsoFrom P S.X₁
  /-- The middle bounded-above complex whose terms satisfy `P`. -/
  middle : Minus.TermsIn P
  /-- The left arrow of the resolving row. -/
  f : leftResolution.model ⟶ middle
  /-- The right arrow of the resolving row. -/
  g : middle ⟶ R.model
  /-- The two arrows of the resolving row have zero composite. -/
  zero : f ≫ g = 0
  /-- The comparison from the underlying resolving row to the source row. -/
  comparison :
    (ShortComplex.mk f g zero).map (Minus.TermsIn.ι P) ⟶ S
  /-- The left component is the comparison of the chosen left resolution. -/
  comparison_left : comparison.τ₁ = leftResolution.comparison
  /-- The right component is the comparison of the prescribed resolution. -/
  comparison_right : comparison.τ₃ = R.comparison
  /-- The underlying resolving row is short exact. -/
  shortExact :
    ((ShortComplex.mk f g zero).map (Minus.TermsIn.ι P)).ShortExact

attribute [simp] Horseshoe.comparison_left Horseshoe.comparison_right

namespace Horseshoe

variable {S : ShortComplex (CochainComplex A ℤ)}
  {R : QuasiIsoFrom P S.X₃}

/-- The resolving row of bounded-above termwise-`P` complexes in a horseshoe. -/
abbrev row (H : Horseshoe S R) : ShortComplex (Minus.TermsIn P) :=
  ShortComplex.mk H.f H.g H.zero

/-- The named resolving row remains short exact after forgetting to cochain complexes. -/
theorem row_shortExact (H : Horseshoe S R) :
    (H.row.map (Minus.TermsIn.ι P)).ShortExact := sorry

/-- The degree-`n` short complex underlying the resolving row. -/
abbrev rowEval (H : Horseshoe S R) (n : ℤ) : ShortComplex A :=
  (H.row.map (Minus.TermsIn.ι P)).map
    (HomologicalComplex.eval A (ComplexShape.up ℤ) n)

/-- The degree-`n` resolving row is short exact. -/
theorem rowEval_shortExact (H : Horseshoe S R) (n : ℤ) :
    (H.rowEval n).ShortExact := sorry

/-- The left object of the resolving row is the chosen left model. -/
@[simp]
theorem row_X₁ (H : Horseshoe S R) : H.row.X₁ = H.leftResolution.model := sorry

/-- The middle object of the resolving row is the horseshoe middle model. -/
@[simp]
theorem row_X₂ (H : Horseshoe S R) : H.row.X₂ = H.middle := sorry

/-- The right object of the resolving row is the prescribed model. -/
@[simp]
theorem row_X₃ (H : Horseshoe S R) : H.row.X₃ = R.model := sorry

/-- The left arrow of the resolving row is the horseshoe left model morphism. -/
@[simp]
theorem row_f (H : Horseshoe S R) : H.row.f = H.f := sorry

/-- The right arrow of the resolving row is the horseshoe right model morphism. -/
@[simp]
theorem row_g (H : Horseshoe S R) : H.row.g = H.g := sorry

/-- The comparison from the resolving row to the source row, expressed through `row`. -/
abbrev rowComparison (H : Horseshoe S R) : H.row.map (Minus.TermsIn.ι P) ⟶ S :=
  H.comparison

/-- The middle component of the comparison carried by a property-indexed horseshoe. -/
abbrev middleComparison (H : Horseshoe S R) :
    (H.middle : CochainComplex A ℤ) ⟶ S.X₂ :=
  H.comparison.τ₂

/-- The left component of the row comparison is the chosen left-resolution comparison. -/
@[simp]
theorem rowComparison_τ₁ (H : Horseshoe S R) :
    H.rowComparison.τ₁ = H.leftResolution.comparison := sorry

/-- The middle component of the row comparison is the horseshoe middle comparison. -/
@[simp]
theorem rowComparison_τ₂ (H : Horseshoe S R) :
    H.rowComparison.τ₂ = H.middleComparison := sorry

/-- The right component of the row comparison is the prescribed resolution comparison. -/
@[simp]
theorem rowComparison_τ₃ (H : Horseshoe S R) :
    H.rowComparison.τ₃ = R.comparison := sorry

/-- The left component of a property-indexed horseshoe comparison is a quasi-isomorphism. -/
theorem leftComparison_quasiIso (H : Horseshoe S R) :
    QuasiIso H.comparison.τ₁ := sorry

/-- The right component of a property-indexed horseshoe comparison is a quasi-isomorphism. -/
theorem rightComparison_quasiIso (H : Horseshoe S R) :
    QuasiIso H.comparison.τ₃ := sorry

/-- The middle component of a property-indexed horseshoe comparison is a quasi-isomorphism. -/
theorem middleComparison_quasiIso (H : Horseshoe S R) :
    QuasiIso H.middleComparison := sorry

/-- The property-indexed bounded-above resolution of the middle term supplied by a horseshoe. -/
@[stacks 064C "middle resolution of a property-indexed bounded-above horseshoe"]
def middleResolution (H : Horseshoe S R) : QuasiIsoFrom P S.X₂ :=
  QuasiIsoFrom.mk H.middle H.middleComparison H.middleComparison_quasiIso

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


end CochainComplex.Minus.TermsIn.QuasiIsoFrom
