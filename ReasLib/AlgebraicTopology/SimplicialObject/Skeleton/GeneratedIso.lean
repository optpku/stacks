/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Generated.Abelian

/-!
# Compatibility import for the skeleton-generated isomorphism

The reusable comparison API lives in `Skeleton.Counit.Subobject` and
`Skeleton.Generated.Comparison`, while `Skeleton.Generated.Abelian` owns the canonical abelian
comparisons and imports `Skeleton.Counit.Abelian` for counit monomorphisms.  This legacy module
keeps the earlier aggregate import path available without owning additional declarations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Skeleton

end CategoryTheory.SimplicialObject.Skeleton
