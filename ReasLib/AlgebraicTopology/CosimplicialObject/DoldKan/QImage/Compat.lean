module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Comparison
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.NormalizedComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Source-facing compatibility for canonical Dold--Kan images

This facade intentionally owns only the comparison from the historical degreewise
span/quotient presentations to the canonical `QInfty` image model.  Import it when a
source-facing statement is required; canonical clients should import `QImage` or its
semantic leaves instead.

@stack 019I
-/

@[expose] public section
