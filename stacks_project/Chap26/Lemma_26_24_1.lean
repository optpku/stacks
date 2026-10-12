/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.24.1: qcqs pushforward preserves quasi-coherent modules. -/
@[stacks 01LC]
#check Scheme.Modules.pushforward.isQuasicoherent

#check Scheme.QCoh.pushforward.mapsTo
#check Scheme.QCoh.pushforward
#check Scheme.QCoh.pushforward.inclusionIso
#check Scheme.QCoh.pushforward.idIso
#check Scheme.QCoh.pushforward.compIso
#check Scheme.QCoh.pushforward.congrIso
#check Scheme.QCoh.pushforward.compIso.associativity
#check Scheme.QCoh.pushforward.compIso.left_unit
#check Scheme.QCoh.pushforward.compIso.right_unit
#check Scheme.QCoh.pushforward.obj_obj
#check Scheme.QCoh.pushforward.map_hom
#check Scheme.Modules.pushforward.isQuasicoherentOf
#check Scheme.Modules.pushforwardComp.associativity
#check Scheme.Modules.pushforwardComp.left_unit
#check Scheme.Modules.pushforwardComp.right_unit
