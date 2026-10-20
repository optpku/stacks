/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Bifunctor
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Constant
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Truncated

/-!
# Functoriality of simplicial copowers

This compatibility facade exports object-variable, constant-object, index-variable,
bifunctorial, and truncated copower APIs. New consumers should import the narrow semantic leaf
owning the declarations they use.
-/

@[expose] public section
