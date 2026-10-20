module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import ReasLib.RingTheory.QuasiFinite.FiniteType
import StacksCheckRecall

/-! @stack 02UR -/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
- primary domain: local quasi-finiteness for finite-type unramified algebra maps;
- sampled owner declarations:
  `Algebra.IsUnramifiedAt`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.FiniteType.QuasiFiniteAt`,
  `Algebra.FiniteType.QuasiFiniteAt.of_quasiFiniteAt`;
- best owner abstraction: the chapter's source-facing owner
  `Algebra.FiniteType.QuasiFiniteAt`, whose mathematical core is the canonical local owner
  `Algebra.QuasiFiniteAt`;
- source/core/bridge triage:
  `source-facing`: `Algebra.FiniteType.QuasiFiniteAt R S q` from Definition `10.122.3`;
  `core/canonical`: `Algebra.QuasiFiniteAt R q`;
  `bridge/view`: `Algebra.FiniteType.QuasiFiniteAt.of_quasiFiniteAt`;
- primitive data vs derived API: finite type and `Algebra.IsUnramifiedAt R q` are the primitive
  hypotheses. The quasi-finite conclusion is already the canonical owner instance
  `Algebra.QuasiFiniteAt R q`, and the chapter source-facing predicate is derived from it via the
  bridge in Definition `10.122.3`.
-/

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

variable [Algebra.FiniteType R S]
variable (q : Ideal S) [q.IsPrime] [Algebra.IsUnramifiedAt R q]

@[stacks 02UR "unramified implies quasi-finite at a prime"]
#check (inferInstance : Algebra.QuasiFiniteAt R q)

@[stacks 02UR "finite-type quasi-finite source predicate"]
#check @Algebra.FiniteType.QuasiFiniteAt.of_quasiFiniteAt

end
