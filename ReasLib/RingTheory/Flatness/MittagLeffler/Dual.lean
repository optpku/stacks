/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.FiniteFree
public import ReasLib.RingTheory.Flatness.MittagLeffler

/-!
# The dual criterion for Mittag-Leffler presentations

For a directed system of finite free modules, it is enough to test the Mittag-Leffler condition
on the inverse system obtained by applying `Hom(-, R)`. This file records that criterion at the
directed-system, presentation-data, and presented-module layers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace Module.IsMittagLefflerDirectedSystem

variable {R : Type u} [CommRing R]
variable {I : Type w} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- A directed system of finite free modules is Mittag-Leffler when its inverse system of
`R`-linear duals is Mittag-Leffler. -/
@[stacks 059G "directed system"]
theorem of_dual (F : I ⥤ ModuleCat.{max u w} R)
    (hff : ∀ i, CategoryTheory.ModuleCat.finiteFree R (F.obj i))
    (hdual : (F.homInverseSystem
      (ModuleCat.of.{max u w} R (ULift.{max u w} R))).IsMittagLeffler) :
    IsMittagLefflerDirectedSystem F := sorry

/-- For a directed system of finite free modules, the universal Hom-system criterion is
equivalent to the single dual-system test with target `R`. -/
@[stacks 059G "dual criterion iff"]
theorem iff_dual (F : I ⥤ ModuleCat.{max u w} R)
    (hff : ∀ i, CategoryTheory.ModuleCat.finiteFree R (F.obj i)) :
    IsMittagLefflerDirectedSystem F ↔
      (F.homInverseSystem
        (ModuleCat.of.{max u w} R (ULift.{max u w} R))).IsMittagLeffler := sorry

end Module.IsMittagLefflerDirectedSystem

namespace Module.MittagLeffler

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {I : Type w} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- Build reusable Mittag-Leffler presentation data from a finite free presentation whose
inverse system of duals is Mittag-Leffler. -/
@[stacks 059G "presentation data"]
def Presentation.ofDual
    (P : ColimitPresentation I
      (ModuleCat.of.{max u w} R (ULift.{max u w} M)))
    (hff : ∀ i, CategoryTheory.ModuleCat.finiteFree R (P.diag.obj i))
    (hdual : (P.diag.homInverseSystem
      (ModuleCat.of.{max u w} R (ULift.{max u w} R))).IsMittagLeffler) :
    Presentation.{u, u, w} R M :=
  Presentation.ofColimit P
    (Module.IsMittagLefflerDirectedSystem.of_dual P.diag hff hdual)

/-- Remark 10.88.8, tag `059G`: a module with a finite free directed presentation is
Mittag-Leffler if the inverse system of duals of its stages is Mittag-Leffler. -/
@[stacks 059G]
theorem of_dualPresentation
    (P : ColimitPresentation I
      (ModuleCat.of.{max u w} R (ULift.{max u w} M)))
    (hff : ∀ i, CategoryTheory.ModuleCat.finiteFree R (P.diag.obj i))
    (hdual : (P.diag.homInverseSystem
      (ModuleCat.of.{max u w} R (ULift.{max u w} R))).IsMittagLeffler) :
    MittagLeffler R M := sorry

/-- Source-facing form of `Module.MittagLeffler.of_dualPresentation` for a diagram equipped
with an isomorphism from its chosen colimit to the presented module. -/
@[stacks 059G "chosen colimit"]
theorem of_dualColimit (F : I ⥤ ModuleCat.{max u w} R) [HasColimit F]
    (c : colimit F ≅
      ModuleCat.of.{max u w} R (ULift.{max u w} M))
    (hff : ∀ i, CategoryTheory.ModuleCat.finiteFree R (F.obj i))
    (hdual : (F.homInverseSystem
      (ModuleCat.of.{max u w} R (ULift.{max u w} R))).IsMittagLeffler) :
    MittagLeffler R M := sorry

end Module.MittagLeffler
