/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Over

/-!
# Inherited topology for bundled fibered categories

The canonical construction is `Functor.inheritedTopology`, which applies to an arbitrary
projection functor. For a bundled fibred category `P`, use
`P.p.inheritedTopology J` directly.
-/

@[expose] public section

namespace CategoryTheory

end CategoryTheory
