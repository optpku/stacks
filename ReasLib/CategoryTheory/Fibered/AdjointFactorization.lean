/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Basic
public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Projections
public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Inclusion
public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Adjunction
public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Presheaf

/-!
# Adjoint factorization of a morphism of fibred categories

Compatibility aggregate for the vertical-comma adjoint factorization API.

New developments should import the smallest leaf matching their use:

* `Basic` for the vertical-comma carrier and intermediate fibred category;
* `Projections` for source and target factorization legs;
* `Inclusion` for the fully faithful identity-comparison inclusion;
* `Adjunction` for the adjunction and source-facing existence theorem.
* `Presheaf` for coefficient pullback along the source endpoint and its fiberwise restriction.
-/
