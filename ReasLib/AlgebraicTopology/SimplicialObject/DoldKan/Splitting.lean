module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Splitting.Decomposition
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Splitting.LowerFace
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Splitting.Normalized

/-!
# Lower-face and normalized Dold--Kan splittings

Compatibility facade for the splitting API. New files can import `Decomposition`, `LowerFace`, or
`Normalized` directly according to the layer they use; this module keeps the historical aggregate
import available to downstream chapter files.
-/
