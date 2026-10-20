/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Topology.Sheaves.Types.Morphisms

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 6.16.3:
- primary domain: mono/epi criteria for set-valued presheaves and sheaves on a topological space;
- inspected owner declarations:
  `NatTrans.epi_iff_epi_app`, `NatTrans.mono_iff_mono_app`,
  `TopCat.Sheaf.isLocallySurjective_iff_epi`,
  `TopCat.Sheaf.epi_iff_stalk_surjective`.
- best owner abstraction: the categorical predicates `Mono φ` and `Epi φ` on morphisms of
  presheaves/sheaves, with sectionwise, local, and stalkwise injectivity/surjectivity criteria as
  derived API.

Primitive-vs-derived split:
- primitive data: the canonical categorical notions `Mono` and `Epi` for the morphism itself;
- derived API: objectwise injectivity/surjectivity on sections, local surjectivity, and stalkwise
  injectivity/surjectivity.

Source/core/bridge triage:
- `source-facing`: the textbook criteria for monomorphisms and epimorphisms of presheaves and
  sheaves of sets;
- `core/canonical`: the owner predicates `Mono`, `Epi`, and the mathlib owner
  `TopCat.Presheaf.IsLocallySurjective`;
- `bridge/view`: the equivalences between those owner predicates and sectionwise/local/stalkwise
  criteria. -/

/- Lemma 6.16.3 (1): for set-valued presheaves on `X`, epimorphisms are
exactly the morphisms that are surjective on sections over every open set. This is the
source-facing bridge theorem recorded in Definition 6.16.2. -/
@[stacks 0H7H "presheaf epimorphisms are sectionwise surjective"]
recall CategoryTheory.NatTrans.epi_iff_epi_app

/- In `Type`, component epimorphisms are exactly surjective functions. -/
recall CategoryTheory.epi_iff_surjective

/- Lemma 6.16.3 (2): for set-valued presheaves on `X`, monomorphisms are
exactly the morphisms that are injective on sections over every open set. This is the
source-facing bridge theorem recorded in Definition 6.16.2. -/
@[stacks 0H7H "presheaf monomorphisms are sectionwise injective"]
recall CategoryTheory.NatTrans.mono_iff_mono_app

/- In `Type`, component monomorphisms are exactly injective functions. -/
recall CategoryTheory.mono_iff_injective

/- Lemma 6.16.3 (3): for set-valued sheaves, epimorphisms are exactly
surjective morphisms in the source sense of admitting local lifts of sections. -/
@[stacks 0H7H "sheaf epimorphisms are surjective"]
recall TopCat.Sheaf.isLocallySurjective_iff_epi

/- Lemma 6.16.3 (4): for set-valued sheaves on `X`,
epimorphisms are exactly the morphisms that are surjective on all stalks. This is the exact
canonical theorem already recorded in Lemma 6.16.1. -/
@[stacks 0H7H "sheaf epimorphisms are stalkwise surjective"]
recall TopCat.Sheaf.epi_iff_stalk_surjective

/- Lemma 6.16.3 (5): for set-valued sheaves on `X`,
monomorphisms are exactly the morphisms that are injective on sections over every open set. This
is the exact canonical theorem already recorded in Definition 6.16.2. -/
@[stacks 0H7H "sheaf monomorphisms are sectionwise injective"]
recall CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono

/- Lemma 6.16.3 (6): for set-valued sheaves on `X`,
monomorphisms are exactly the morphisms that are injective on all stalks. This is the exact
canonical theorem already recorded in Lemma 6.16.1. -/
@[stacks 0H7H "sheaf monomorphisms are stalkwise injective"]
recall TopCat.Sheaf.mono_iff_stalk_injective
