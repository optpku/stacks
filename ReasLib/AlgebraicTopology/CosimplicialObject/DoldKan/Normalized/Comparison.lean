module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Normalized.MooreComparison
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.NormalizedComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Normalized comparison compatibility facade

The source quotient versus `QInfty` image comparison, including its canonical split section,
lives in `QImage.NormalizedComparison` under source/image hypotheses.  The independent comparison
with the transported Moore model lives in `Normalized.MooreComparison`.  This historical import
path re-exports both APIs without adding an Abelian wrapper around the reusable quotient bridge.
-/

@[expose] public section

-- The source quotient and canonical image quotient comparison API.
/- 019I: normalized quotient comparison compatibility facade. -/

-- The transported Moore model comparison API.
