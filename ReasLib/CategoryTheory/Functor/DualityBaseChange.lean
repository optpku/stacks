/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Opposites

/-!
# Duality base-change maps

A base-change component induces a morphism between the corresponding values of a chosen
contravariant-covariant Hom functor by functoriality in its second argument.
Use `(rHom.obj (Opposite.op M)).map baseChange` directly; the morphism operation and its
functoriality API belong to `CategoryTheory.Functor`.
-/
