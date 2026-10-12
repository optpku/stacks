/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent
import StacksCheckRecall

universe u

open AlgebraicGeometry

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/- Definition 39.14.1: The objects of `GroupoidScheme.QCoh G` are quasi-coherent
modules `F` on `G.U.left` equipped with an action map `t^*F ⟶ s^*F` satisfying
the cocycle and unit laws. -/
@[stacks 03LI] #check (AlgebraicGeometry.GroupoidScheme.QCoh G : CategoryTheory.Cat)

/- Companion check: an equivariant quasi-coherent module is constructed from
`F`, its action map, and proofs of the cocycle and unit laws. -/
#check GroupoidScheme.QCoh.of

/- Companion check: `obj` and `action` recover the underlying quasi-coherent
module and the map `t^*F ⟶ s^*F`. -/
#check GroupoidScheme.QCoh.obj
#check GroupoidScheme.QCoh.action

/- Companion check: the bundled system exposes the two defining laws. -/
#check AlgebraicGeometry.GroupoidScheme.System.spec
#check GroupoidScheme.System.cocycle
#check GroupoidScheme.System.unit
