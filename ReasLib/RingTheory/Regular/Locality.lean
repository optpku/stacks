/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalProperties.Basic
public import ReasLib.RingTheory.Regular.RingMap

/-!
# Locality of regular ring homomorphisms

This file records that regularity is a local property of commutative ring homomorphisms.
-/

@[expose] public section

namespace RingHom.Regular

/-- Regularity is a local property of commutative ring homomorphisms. -/
theorem propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.Regular := sorry

end RingHom.Regular
