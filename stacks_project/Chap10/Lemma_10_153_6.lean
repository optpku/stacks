/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselian.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Strictly henselian finite-type decompositions

@stack 06DD

The reusable data owners are `Algebra.FinitePartDecomposition` for the
finite-part/remainder split and `HenselianLocalRing.FiniteProduct` for the
finite local factors.  This source-facing result adds the strictly henselian
residue-field conclusion to those two independent presentations.

The local-map and henselian-local consequences of finite factors are owned by
`Algebra.isLocalHom_of_moduleFinite` and
`HenselianLocalRing.of_moduleFinite`; they are derived API rather than fields
of this statement.
-/

@[stacks 06DD "strictly henselian finite-type decomposition"]
#check @StrictHenselianLocalRing.FiniteType.existsFinitePartDecomposition
