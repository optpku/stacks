/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.Syntomic.Properties

@[expose] public section

/-!
# Syntomic Principal-Open Locality Recall

The source statement is owned by the intrinsic `RingHom.Syntomic` predicate.
The ReasLib leaves expose both the forward principal-localization statements
and the finite-cover locality witnesses without exposing proof plumbing.

@stack 00SO
-/

/- Lemma 10.136.4, tag 00SO: for a finite principal-open cover of `Spec S`,
the map `R → S` has local-complete-intersection fibers, respectively is
syntomic, exactly when the corresponding localized maps do. -/
@[stacks 00SO "syntomic locality on the target"]
#check @RingHom.Syntomic.ofLocalizationSpanTarget

#check @RingHom.HasLocalCompleteIntersectionFibers.ofLocalizationSpanTarget

#check @RingHom.Syntomic.localizationAway

#check @RingHom.HasLocalCompleteIntersectionFibers.localizationAway

#check @RingHom.Syntomic.propertyIsLocal

#check @RingHom.Syntomic.iff_forall_atPrime
