/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.PurelyInseparable.Lift
import StacksCheckRecall

/-!
# Lemma 10.42.4: transcendence-basis stage support

@stack 04KM
-/

@[expose] public section

/- Lemma 10.42.4: a finitely generated field extension admits a finite purely inseparable lift
whose top extension is separably generated over the lifted base.  The canonical owner packages
the two field extensions, all scalar-tower data, and the five source conditions in `Lift.spec`. -/
@[stacks 04KM "finite purely inseparable lift to a separably generated extension"]
#check @FieldExtension.PurelyInseparable.Lift.existsOfEssFiniteType

/- The specification companion exposes the concrete finite-dimensional and purely inseparable
edges together with separable generation, rather than hiding them behind an existential alias. -/
@[stacks 04KM "finite purely inseparable lift specification"]
#check @FieldExtension.PurelyInseparable.Lift.spec
