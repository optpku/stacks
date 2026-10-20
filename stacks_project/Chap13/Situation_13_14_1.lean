/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.CategoryTheory.Localization.Triangulated
import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
import StacksCheckRecall

@[expose] public section

/-
Domain-style sampling:
- primary domain: exact-localization situations for triangulated categories, assembled from the
  chapter owners in Definitions `13.3.3`, `4.27.20`, and `13.5.1`;
- inspected canonical declarations in that domain:
  `CategoryTheory.IsTriangulated`,
  `CategoryTheory.Functor.CommShift ℤ`,
  `CategoryTheory.Functor.IsTriangulated`,
  `CategoryTheory.MorphismProperty.IsSaturatedMultiplicativeSystem`,
  `CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation`;
- best owner abstraction: no new bundled “situation” structure is mathematically present here.
  Situation `13.14.1` is the simultaneous availability of those five existing owners for the
  pair `(F, S)`.

Primitive-vs-derived split:
- primitive data: exactly those five owner classes, with no extra situation wrapper;
- derived API: all localization and derived-functor consequences proved later in Chapter `13`,
  which should take these owner assumptions directly rather than through a parallel wrapper.

Source/core/bridge triage:
- `source-facing`: the textbook setup consisting of an exact functor `F` and a saturated
  triangulation-compatible multiplicative system `S`;
- `core/canonical`: the five owner classes listed above;
- `bridge/view`: downstream constructions such as the restricted derived functors and induced
  triangulated-localization structures.
-/

/- Situation 13.14.1 assumes that both ambient categories are triangulated. -/
@[stacks 05S8 "ambient triangulated categories"]
#check @CategoryTheory.IsTriangulated

/- Its exact functor carries coherent shift-compatibility data. -/
@[stacks 05S8 "shift compatibility of the exact functor"]
#check @CategoryTheory.Functor.CommShift

/- Preservation of distinguished triangles is owned by `Functor.IsTriangulated`. -/
@[stacks 05S8 "exactness of the functor"]
#check @CategoryTheory.Functor.IsTriangulated

/- The localization class is a saturated multiplicative system. -/
@[stacks 05S8 "saturated multiplicative system"]
#check @CategoryTheory.MorphismProperty.IsSaturatedMultiplicativeSystem

/- The localization class is compatible with the ambient triangulation. -/
@[stacks 05S8 "compatibility with triangulation"]
#check @CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation
