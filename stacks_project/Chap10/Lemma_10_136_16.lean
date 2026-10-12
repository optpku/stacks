/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Syntomic.Conormal
import StacksCheckRecall

@[expose] public section

/-!
# Localized Conormal Modules of Syntomic Presentations

@stack 07BT

The reusable inputs are the canonical `RingHom.Syntomic` predicate, the quotient-ideal cotangent
module, and its localization away from a quotient element.  Relative complete-intersection charts
and stable cotangent comparisons belong to the proof layer and are not re-exported here.
-/

/- Lemma 10.136.16 (07BT): if the localization of an explicit polynomial quotient is syntomic
over `R`, then the localized conormal module is finite projective.

The Stacks statement assumes the presentation ideal is finitely generated.  The canonical
Syntomic formulation below does not need that redundant hypothesis in its public interface. -/
@[stacks 07BT "finite localized conormal module"]
#check @RingHom.Syntomic.idealCotangent_localizedAway_finite

@[stacks 07BT "projective localized conormal module"]
#check @RingHom.Syntomic.idealCotangent_localizedAway_projective
