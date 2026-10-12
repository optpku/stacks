/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.Index
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.SourceIndex
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.Sum
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.SourceSum
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.ShortComplex

/-!
# Eilenberg-MacLane extensions

Compatibility facade for the independent extension-index, degreewise-sum, and short-complex
interfaces. New downstream files should import the narrow semantic leaf they use.
-/
