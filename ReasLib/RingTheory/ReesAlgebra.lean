/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Grading
public import ReasLib.RingTheory.ReesAlgebra.Presentation
public import ReasLib.RingTheory.ReesAlgebra.Presentation.Coordinate
public import ReasLib.RingTheory.ReesAlgebra.Scaling
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Lift
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Map
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Localization
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Presentation
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Coordinate
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Spectrum
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Scaling
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.FractionField
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Valuation
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.BaseChange
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Domain
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Radical
public import ReasLib.RingTheory.ReesAlgebra.Reduced
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Reduced

/-!
# Rees algebras

Fine-grained reusable infrastructure for the canonical grading of Rees
algebras and their affine homogeneous-localization charts.

@stack 052Q
-/

-- Definition 10.70.1 (052Q), recalled through the shared Rees-algebra API.
