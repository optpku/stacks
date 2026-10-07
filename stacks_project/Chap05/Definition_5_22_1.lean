module

public import Mathlib.Topology.Category.Profinite.AsLimit
import StacksCheckRecall

@[expose] public section

/-
Mathlib's bundled `Profinite` type is the canonical owner of the notion, while
`Profinite.fintypeDiagram`, `Profinite.diagram`, and `Profinite.lim` give the source's equivalent
presentation as a limit of finite discrete spaces. Recalling that owner and its canonical limit
cone avoids a parallel existential predicate and makes the actual diagram and limit data directly
available to later items.
-/

/- Definition 5.22.1: a profinite space is represented by the canonical bundled type
`Profinite`; the recalls below exhibit every such space as a limit of finite discrete spaces. -/
@[stacks 08ZX "profinite spaces via the canonical bundled owner"]
#check Profinite

/- Finite types with their discrete topology define the finite profinite spaces in the limit
presentation. -/
#check FintypeCat.toProfinite

/- The canonical diagram of finite discrete quotients of a profinite space. -/
#check Profinite.fintypeDiagram

/- The canonical profinite-valued finite-discrete diagram. -/
#check Profinite.diagram

/- Every profinite space is the limit point of its canonical diagram of finite discrete spaces. -/
#check Profinite.lim
