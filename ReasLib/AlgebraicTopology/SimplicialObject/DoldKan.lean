module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace.Signed
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace.Decomposition
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace.Acyclic
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Splitting
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Reflects
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.Homotopy
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.TrivialKanFibration
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.UnderlyingHomotopyEquivalence
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.UnderlyingHomotopyEquivalence.Functor
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.UnderlyingHomotopyEquivalence.ModuleCat

/-!
# Simplicial-object Dold--Kan support

This import aggregate exports reusable constructions attached directly to simplicial objects:
the functorial normalized Moore splitting, its lower-face counterpart, Dold--Kan fullness for the
normalized-Moore homotopy comparison, and the quasi-isomorphism criterion for homotopy
equivalences after forgetting simplicial abelian groups to simplicial sets.  The latter is also
exported through arbitrary additive homology-preserving conservative functors and its module
specialization.
-/

@[expose] public section
