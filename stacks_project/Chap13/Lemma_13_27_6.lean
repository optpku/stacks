/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Abelian.Extension.Classification
import StacksCheckRecall

@[expose] public section

/- Domain-style sampling for Lemma 13.27.6:
- primary domain: degree-one `Ext` in an abelian category and its classification by extension
  classes;
- sampled owner declarations:
  `ExtensionClass`,
  `ExtensionClass.toExt`,
  `ExtensionClass.toExtAddHom`,
  `ExtensionClass.toExt_bijective`,
  `Ext B A 1`;
- best owner abstraction: the canonical owner is `Ext B A 1`, while the source-facing extension
  group is `ExtensionClass A B`; the correct bridge for this lemma is the additive map
  `ExtensionClass.toExtAddHom` together with `ExtensionClass.toExt_bijective`;
- primitive-vs-derived split:
  primitive data: the ambient abelian category with `HasExt` and the objects `A`, `B`;
  derived API: the additive identification of the Chapter 12 extension group with `Ext B A 1`.

Source/core/bridge triage:
- `source-facing`: `ExtensionClass A B`;
- `core/canonical`: `Ext B A 1`;
- `bridge/view`: `ExtensionClass.toExtAddHom` and `ExtensionClass.toExt_bijective`.

This file should therefore stay at the bridge layer: it recalls the canonical additive map and its
bijectivity between the source-facing extension group and the owner `Ext¹`, without introducing
any parallel local alias or choosing an inverse from deferred proof debt.
-/

/- Lemma 13.27.6: in an abelian category, the extension group constructed from short exact
sequences is classified by the canonical additive map `ExtensionClass.toExtAddHom` to `Ext¹(B, A)`,
whose underlying map is bijective by `ExtensionClass.toExt_bijective`. -/
#check @CategoryTheory.ExtensionClass.toExtAddHom
@[stacks 06XV] #check @CategoryTheory.ExtensionClass.toExt_bijective
