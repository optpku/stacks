/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Extension.Degree
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (E : Type u) (F : Type v) [Field E] [Field F] [Algebra E F]

/- Source/core/bridge triage for Definition 9.7.1:
- `source-facing`: the textbook degree notation `[F : E]`
- `core/canonical`: `Module.rank E F`
- `bridge/view`: `FiniteDimensional E F` and `Module.finrank E F` for the finite-degree case

Primitive data are only the field extension and its canonical `E`-module structure on `F`. The
finite-dimensionality predicate and natural-number degree are derived API, so the shared owner
exposes notation on `Module.rank` and this source file only checks that interface.
-/

open scoped FieldExtensionDegree

/- Definition 9.7.1 (Tag 09G3): the textbook degree notation `[F : E]` denotes the cardinal
dimension of `F` as an `E`-vector space. -/
@[stacks 09G3]
#check ([F : E] : Cardinal)

/-
For a field extension `F/E`, the degree `[F : E]` is the dimension
of `F` as an `E`-vector space. The shared notation is a view of the canonical owner
`Module.rank E F`.
-/
#check Module.rank

/- Definition 9.7.1 also uses the canonical `FiniteDimensional E F` typeclass for the notion that
the field extension `F/E` is finite. -/
#check FiniteDimensional

/- Companion check: `Module.finrank E F` is the canonical natural-number view of the same degree;
by definition it is `Cardinal.toNat (Module.rank E F)`, so `Cardinal.toNat [F : E]` already
reduces to `Module.finrank E F`. -/
#check Module.finrank
