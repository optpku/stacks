/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.FiniteType
public import ReasLib.RingTheory.Excellent
public import ReasLib.RingTheory.Regular.GRing.EssentialFiniteness
public import ReasLib.RingTheory.Regular.JRing.EssentialFiniteness

@[expose] public section

/-!
# Excellence and Essential Finiteness

@stack 07QU
@stack 07QW
-/

universe u v w

namespace IsQuasiExcellentRing

/-- Finite type algebras over quasi-excellent rings are quasi-excellent. -/
@[stacks 07QU "finite type quasi-excellence"]
theorem of_finiteType
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsQuasiExcellentRing.{u, w} R] [Algebra.FiniteType R S] :
    IsQuasiExcellentRing.{v, w} S := sorry

/-- Essentially finite type algebras over quasi-excellent rings are quasi-excellent. -/
@[stacks 07QU "essentially finite type quasi-excellence"]
theorem of_essFiniteType
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsQuasiExcellentRing.{u, w} R] [Algebra.EssFiniteType R S] :
    IsQuasiExcellentRing.{v, w} S := sorry

end IsQuasiExcellentRing

namespace IsExcellentRing

/-- Finite type algebras over excellent rings are excellent. -/
@[stacks 07QW "finite type excellence"]
theorem of_finiteType
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsExcellentRing.{u, w} R] [Algebra.FiniteType R S] :
    IsExcellentRing.{v, w} S := sorry

/-- Essentially finite type algebras over excellent rings are excellent. -/
@[stacks 07QU "essentially finite type excellence"]
theorem of_essFiniteType
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsExcellentRing.{u, w} R] [Algebra.EssFiniteType R S] :
    IsExcellentRing.{v, w} S := sorry

end IsExcellentRing
