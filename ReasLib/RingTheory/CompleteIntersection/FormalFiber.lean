/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.FormalFiber.FieldProperty.Laws
public import ReasLib.RingTheory.RingHom.Syntomic.Basic
public import ReasLib.RingTheory.FormalFiber.LocalCompleteIntersection

/-!
# Local complete-intersection formal fibers

This leaf names the local-complete-intersection condition on the formal fibers
of a local ring and records that the condition does not hold for every
Noetherian local ring.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace FieldAlgebraProperty

/- The canonical field-algebra property underlying local-complete-intersection formal fibers. -/

/-- The intrinsic local-complete-intersection ring property, retained under the legacy
formal-fiber name. It is independent of the displayed ground field and imposes no finite
presentation condition over that field. -/
@[stacks 09QC "local complete-intersection field-algebra property"]
abbrev localCompleteIntersection : FieldAlgebraProperty.{u, v} :=
  localCompleteIntersectionRing

/-- Intrinsic local complete intersections satisfy the permanence laws used by the formal-fiber
machine, by the canonical ring-property instance. -/
@[stacks 09QC "complete-intersection formal-fiber laws"]
instance localCompleteIntersection.formalFiberLaws :
    (localCompleteIntersection : FieldAlgebraProperty.{u, u}).FormalFiberLaws :=
  localCompleteIntersectionRing.formalFiberLaws

end FieldAlgebraProperty

namespace IsLocalRing

/-- A local ring has LCI formal fibers when every fiber of its maximal-ideal
completion map is intrinsically a local complete-intersection ring. -/
@[stacks 09QC "local complete-intersection formal fibers"]
abbrev HasLciFormalFibers (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  FieldAlgebraProperty.localCompleteIntersectionRing.HoldsOnFormalFibers A

/- This bridge keeps the chapter-facing name while exposing the generic formal-fiber API. -/

/-- A local ring has LCI formal fibers exactly when its formal fibers satisfy the canonical
complete-intersection field-algebra property. -/
@[stacks 09QC "formal fibers as a field-algebra property"]
theorem hasLciFormalFibers_iff (A : Type u) [CommRing A] [IsLocalRing A] :
    HasLciFormalFibers A ↔
      FieldAlgebraProperty.localCompleteIntersection.HoldsOnFormalFibers A := Iff.rfl

/-- Remark 23.9.3 (Tag 09QC): there is a Noetherian local ring whose formal
fibers are not all local complete intersections. -/
@[stacks 09QC]
theorem exists_noetherian_not_hasLciFormalFibers :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsNoetherianRing A),
      ¬ HasLciFormalFibers A := sorry

/-- The LCI formal-fiber condition does not hold for every Noetherian local
ring. -/
@[stacks 09QC "not every Noetherian local ring has LCI formal fibers"]
theorem not_forall_noetherian_hasLciFormalFibers :
    ¬ ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
      HasLciFormalFibers A := sorry

end IsLocalRing

#synth (FieldAlgebraProperty.localCompleteIntersection : FieldAlgebraProperty.{u, u}).EssFiniteTypeBaseChange
#synth (FieldAlgebraProperty.localCompleteIntersection : FieldAlgebraProperty.{u, u}).IsLocal
#synth (FieldAlgebraProperty.localCompleteIntersection : FieldAlgebraProperty.{u, u}).RegularFiberAscent
#synth (FieldAlgebraProperty.localCompleteIntersection : FieldAlgebraProperty.{u, u}).FaithfullyFlatDescent
#synth (FieldAlgebraProperty.localCompleteIntersection : FieldAlgebraProperty.{u, u}).SeparableExtension
