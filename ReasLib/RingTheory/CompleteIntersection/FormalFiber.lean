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

/-- Local complete-intersection algebras over fields, viewed as a reusable field-algebra property.
This is intentionally the local-on-the-spectrum predicate, rather than the stronger global
complete-intersection condition on the whole algebra. -/
@[stacks 09QC "local complete-intersection field-algebra property"]
abbrev localCompleteIntersection : FieldAlgebraProperty.{u, v} :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦
    _root_.IsLocalCompleteIntersection k A

/-- Local complete intersections over fields satisfy the permanence laws used by the formal-fiber
machine.  The individual law classes remain available through this bundled instance. -/
@[stacks 09QC "complete-intersection formal-fiber laws"]
instance localCompleteIntersection.formalFiberLaws :
    (localCompleteIntersection : FieldAlgebraProperty.{u, u}).FormalFiberLaws := sorry

end FieldAlgebraProperty

namespace IsLocalRing

/-- A local ring has LCI formal fibers when every fiber of its maximal-ideal
completion map is a local complete intersection. -/
@[stacks 09QC "local complete-intersection formal fibers"]
abbrev HasLciFormalFibers (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  (algebraMap A (AdicCompletion (maximalIdeal A) A)).HasLocalCompleteIntersectionFibers

/- This bridge keeps the chapter-facing name while exposing the generic formal-fiber API. -/

/-- A local ring has LCI formal fibers exactly when its formal fibers satisfy the canonical
complete-intersection field-algebra property. -/
@[stacks 09QC "formal fibers as a field-algebra property"]
theorem hasLciFormalFibers_iff (A : Type u) [CommRing A] [IsLocalRing A] :
    HasLciFormalFibers A ↔
      FieldAlgebraProperty.localCompleteIntersection.HoldsOnFormalFibers A := sorry

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
