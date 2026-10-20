/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
import StacksCheckRecall

@[expose] public section

/-! @stack 00RS -/

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain triage:
- primary domain: the Jacobi-Zariski exact sequence for Kähler differentials in commutative
  algebra;
- sampled owner declarations: `KaehlerDifferential.map`, `KaehlerDifferential.mapBaseChange`,
  `KaehlerDifferential.exact_mapBaseChange_map`, `KaehlerDifferential.map_surjective`;
- best owner abstraction: the canonical `KaehlerDifferential` maps and their upstream exactness and
  surjectivity theorems;
- layer: `core/canonical`, since Lemma 10.131.7 only recalls the standard exact sequence
  `C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`;
- primitive data: a composable triple of commutative rings `A → B → C`;
- derived API: the induced maps on Kähler differentials together with their exactness and
  surjectivity properties.

The previous file introduced a local conjunction theorem bundling two owner theorems with no new
mathematics. Since that wrapper is unused downstream, the canonical refinement is to recall the
upstream results directly.
-/

/- Lemma 10.131.7: for ring maps `A → B → C`, the canonical sequence
`C ⊗[B] Ω[B⁄A] → Ω[C⁄A] → Ω[C⁄B] → 0`
is expressed upstream by exactness of `KaehlerDifferential.mapBaseChange` followed by the
surjectivity of `KaehlerDifferential.map`. -/
@[stacks 00RS "Jacobi-Zariski exactness for Kähler differentials"]
#check @KaehlerDifferential.exact_mapBaseChange_map

/- Companion recall: the terminal map `Ω[C⁄A] → Ω[C⁄B]` in Lemma 10.131.7 is the canonical
surjective map `KaehlerDifferential.map_surjective`. -/
#check @KaehlerDifferential.map_surjective
