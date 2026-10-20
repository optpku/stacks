/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.GeometricRegularity
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Faithfully Flat Descent of Geometric Regularity

The descent statement is a property of field algebras and does not belong to
the numbered chapter that first uses it.  Its namespace follows the owner
class `Algebra.IsGeometricallyRegular`.

@stack 07NH
-/

@[expose] public section

namespace Algebra.IsGeometricallyRegular

universe u v w

variable {k : Type u} {A : Type v} {B : Type w}
variable [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- Lemma 10.166.3 (Tag 07NH): geometric regularity descends along a faithfully
flat algebra map. -/
@[stacks 07NH]
theorem of_faithfullyFlat
    (hff : (algebraMap A B).FaithfullyFlat) [Algebra.IsGeometricallyRegular k B] :
    Algebra.IsGeometricallyRegular k A := sorry

end Algebra.IsGeometricallyRegular
