/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Coskeleton

/-!
# Compatibility import for coskeleton/internal-hom comparisons

The canonical owner moved to `SimplicialObject.InternalHom.Coskeleton`: the coefficient-valued
skeleton formerly present in this file was a mistranslation of textbook truncation notation.
This import path remains so existing clients can migrate without losing the corrected API.
-/
