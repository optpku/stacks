/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Separable.Generated.GeometricallyNormal
import StacksCheckRecall

@[expose] public section

/-!
# Separable field extensions are geometrically normal

Lemma 10.165.4, tag `0C30`, is owned by the reusable separable
field-extension API.

@stack 0C30
-/

/- Lemma 10.165.4, tag `0C30`: a Stacks-separable field extension is
geometrically normal over its base field. -/
@[stacks 0C30]
#check @Algebra.IsSeparableOver.isGeometricallyNormal
