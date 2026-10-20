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

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/- Domain-style sampling for Definition 9.14.7:
- primary domain: separable closure and separable / inseparable degrees of field extensions;
- sampled owner declarations:
  `separableClosure`,
  `eq_separableClosure_iff`,
  `Field.sepDegree`,
  `Field.insepDegree`;
- best owner abstraction: the textbook degrees are canonically owned by the mathlib declarations
  `Field.sepDegree F E` and `Field.insepDegree F E`, both defined from the intermediate field
  `separableClosure F E` identified in Lemma 9.14.6;
- primitive data: none locally, since the underlying intermediate field and both degree
  constructions are already owned upstream in mathlib;
- derived API: the bridge from the textbook subextension `E_sep` to `separableClosure F E` comes
  from Lemma 9.14.6 via `eq_separableClosure_iff`, while later tower laws and finite-degree
  consequences are downstream theorems on `Field.sepDegree` and `Field.insepDegree`.

Source/core/bridge triage:
- `source-facing`: the textbook separable degree `[E : F]ₛ = [E_sep : F]` and inseparable degree
  `[E : F]ᵢ = [E : E_sep]`;
- `core/canonical`: `Field.sepDegree F E` and `Field.insepDegree F E`;
- `bridge/view`: Lemma 9.14.6, which identifies the source field `E_sep` with the canonical owner
  `separableClosure F E`.

This file should therefore remain a pure check surface. Any local abbreviation or restated degree
definition would only duplicate the existing owner declarations. -/

open scoped FieldExtensionDegree

/- Definition 9.14.7 (Tag 030L): the textbook degree notations `[E : F]ₛ` and `[E : F]ᵢ` denote
the canonical cardinal-valued degree owners. -/
@[stacks 030L]
#check ([E : F]ₛ : Cardinal)
#check ([E : F]ᵢ : Cardinal)

/- Definition 9.14.7: for an algebraic field extension `E / F`, with `E_sep` identified in
Lemma 9.14.6 as `separableClosure F E`, the textbook separable degree `[E : F]ₛ = [E_sep : F]`
is the canonical mathlib notion `Field.sepDegree F E`. -/
#check Field.sepDegree

/- Companion check: for the same extension, the textbook inseparable degree `[E : F]ᵢ =
[E : E_sep]` is the canonical mathlib notion `Field.insepDegree F E`. -/
#check Field.insepDegree
