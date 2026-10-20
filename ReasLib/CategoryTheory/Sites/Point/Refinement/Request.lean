/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.CoverLifting
public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.EssentiallySmall.Fiber

/-!
# Finite-cover requests along refinements

This module owns finite-cover lifting requests for essentially-small inverse
systems and their transport and solution API along ordered refinements.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w r r' q

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

/- The finite-cover lifting requests attached to the object fiber of an
essentially-small inverse system. This is the reusable request owner; it does
not require directedness of the index. -/
namespace EssentiallySmallFiber

variable {C : Type u} [Category.{v} C]
variable {I : Type w} [Category.{r} I]
variable [LocallySmall.{q} C] [EssentiallySmall.{q} Iᵒᵖ]

/- The finite-cover request API specialized to object fibers of essentially-small inverse
systems. -/
namespace CoverLift

/-- A finite-cover lifting request for the object fiber of an essentially-small inverse
system. -/
noncomputable abbrev Request
    (J : GrothendieckTopology C) (S : Iᵒᵖ ⥤ C) : Type (max u v q) :=
  Functor.CoverLift.Request J (EssentiallySmallFiber.fiber S)

end CoverLift
end EssentiallySmallFiber

namespace OrderedRefinement

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} [Preorder ι]
variable {ι' : Type r} [Preorder ι']
variable {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C}
variable {J : GrothendieckTopology C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ] [EssentiallySmall.{q} ι'ᵒᵖ]

/-- Transport a finite-cover lifting request along an order-embedding
refinement of essentially-small inverse systems. -/
noncomputable def mapRequest (R : OrderedRefinement S T)
    (r : EssentiallySmallFiber.CoverLift.Request J S) :
    EssentiallySmallFiber.CoverLift.Request J T :=
  r.map (OrderedRefinement.EssentiallySmall.fiberMap R)

/-- A realized request remains realized after transport along a refinement. -/
theorem mapRequest.isRealized (R : OrderedRefinement S T)
    (r : EssentiallySmallFiber.CoverLift.Request J S) :
    r.is_realized → (R.mapRequest r).is_realized := sorry

/-- A finite-cover lifting request is solved by a pure refinement when its fiber map realizes the
request.  Naming this predicate at the refinement layer avoids repeating the lower-level
`OrderedRefinement.EssentiallySmall.fiberMap` expression in downstream statements. -/
def solves (R : OrderedRefinement S T)
    (r : EssentiallySmallFiber.CoverLift.Request J S) : Prop :=
  r.is_solved_by (OrderedRefinement.EssentiallySmall.fiberMap R)

/-- A pure refinement solves a request exactly when its transported request is realized. -/
@[simp]
theorem solves_iff (R : OrderedRefinement S T)
    (r : EssentiallySmallFiber.CoverLift.Request J S) :
    R.solves r ↔ (R.mapRequest r).is_realized := sorry

/-- Transporting a finite-cover lifting request along the identity refinement leaves it unchanged. -/
@[simp]
theorem id.mapRequest (S : ιᵒᵖ ⥤ C)
    (r : EssentiallySmallFiber.CoverLift.Request J S) :
    (id S).mapRequest r = r := sorry

/-- The identity refinement solves exactly the already-realized requests. -/
@[simp]
theorem id.solves_iff (S : ιᵒᵖ ⥤ C)
    (r : EssentiallySmallFiber.CoverLift.Request J S) :
    (id S).solves r ↔ r.is_realized := sorry

section Composition

variable {ι'' : Type r'} [Preorder ι'']
variable {U : ι''ᵒᵖ ⥤ C}
variable [EssentiallySmall.{q} ι''ᵒᵖ]

/-- Transporting a request along a composite refinement agrees with successive
transport. -/
@[simp]
theorem comp.mapRequest (R : OrderedRefinement S T) (Q : OrderedRefinement T U)
    (r : EssentiallySmallFiber.CoverLift.Request J S) :
    (R.comp Q).mapRequest r = Q.mapRequest (R.mapRequest r) := sorry

/-- A factorization of pure refinements transports a finite-cover lifting request by the
successive request transports.  Unlike `comp.mapRequest`, this eliminates an arbitrary
`IsFactorization` witness rather than requiring the target refinement to be definitionally the
canonical composite. -/
theorem IsFactorization.mapRequest
    {R : OrderedRefinement S T} {Q : OrderedRefinement T U}
    {P : OrderedRefinement S U} (h : IsFactorization R Q P)
    (r : EssentiallySmallFiber.CoverLift.Request J S) :
    P.mapRequest r = Q.mapRequest (R.mapRequest r) := sorry

/-- A request solved by one pure refinement remains solved after a further refinement. -/
theorem comp.solves (R : OrderedRefinement S T) (Q : OrderedRefinement T U)
    (r : EssentiallySmallFiber.CoverLift.Request J S) :
    R.solves r → (R.comp Q).solves r := sorry

/-- A composite refinement solves a request exactly when its second factor
solves the request transported through the first factor. -/
@[simp]
theorem comp.solves_iff (R : OrderedRefinement S T) (Q : OrderedRefinement T U)
    (r : EssentiallySmallFiber.CoverLift.Request J S) :
    (R.comp Q).solves r ↔ Q.solves (R.mapRequest r) := sorry

/-- Along a factorization, solving a source request with the total refinement is equivalent to
solving its transported request with the second refinement. -/
theorem IsFactorization.solves_iff
    {R : OrderedRefinement S T} {Q : OrderedRefinement T U}
    {P : OrderedRefinement S U} (h : IsFactorization R Q P)
    (r : EssentiallySmallFiber.CoverLift.Request J S) :
    P.solves r ↔ Q.solves (R.mapRequest r) := sorry

end Composition

end OrderedRefinement

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
