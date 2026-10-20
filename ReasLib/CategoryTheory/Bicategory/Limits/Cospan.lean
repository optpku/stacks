/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Coherence
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Equivalence.Mk.Coherence
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Coherence
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Functoriality.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Swap.Equivalence

/-!
# Bicategorical cospans

This convenience import assembles the stable public API for bundled bicategorical cospans:
their induced bicategory, projection and coherence computations, componentwise maps,
componentwise equivalences, and endpoint symmetry. It also exposes the focused identity and
composition computation API for functoriality of componentwise mapping.
-/
