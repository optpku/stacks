/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Bifunctor
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Functor.Index

/-!
# Simplicial internal hom

Compatibility facade for the reusable simplicial internal-hom API. Direct consumers should
prefer the narrow semantic leaves `InternalHom.Representability`, `InternalHom.Variance`,
`InternalHom.Functor.Target`, `InternalHom.Functor.Index`, or `InternalHom.Bifunctor`.
-/
