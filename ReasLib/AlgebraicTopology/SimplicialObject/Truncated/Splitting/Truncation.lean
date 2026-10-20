module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Split.Truncation.FromSimplicial
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Split.Truncation.Restriction

/-!
# Truncating split simplicial objects

This compatibility facade re-exports chosen and bundled truncation from ambient simplicial
objects together with restriction between finite truncation levels. Downstream modules should
import the semantic owner leaf matching the bridge they use.
-/

@[expose] public section
