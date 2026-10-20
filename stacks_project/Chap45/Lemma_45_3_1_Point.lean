/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SchemeOverField

#check (point : (k : Type u) → [Field k] → SchemeOverField k)

#check (pointHomIsIso : (k : Type u) → [Field k] → IsIso (point k).hom)

#check (pointIsTerminal :
  (k : Type u) → [Field k] → IsTerminal (point k))

#check (pointIsoTerminal :
  (k : Type u) → [Field k] → point k ≅ ⊤_ (SchemeOverField k))

end AlgebraicGeometry.SchemeOverField
