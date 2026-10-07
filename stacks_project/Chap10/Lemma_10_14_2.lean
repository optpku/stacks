module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

/-!
# Lemma 10.14.2 compatibility entry point

The four finiteness assertions are recalled from the canonical Mathlib owners
`Module.Finite`, `Module.FinitePresentation`, `Algebra.FiniteType`, and
`Algebra.FinitePresentation`; no chapter-specific finiteness wrapper is needed.

@stack 05G5
-/

universe u

/-
Domain-style sampling:
- primary domain: finiteness conditions for modules and algebras under tensor-product base change;
- sampled owner declarations:
  `Module.Finite.base_change`,
  the tensor-product base-change instance for `Module.FinitePresentation`,
  `Algebra.FiniteType.baseChange`,
  `Algebra.FinitePresentation.baseChange`;
- best owner abstraction: the canonical finiteness owners `Module.Finite`,
  `Module.FinitePresentation`, `Algebra.FiniteType`, and `Algebra.FinitePresentation`;
- primitive data: the ring maps `R → S`, `R → R'`, and the original finiteness hypotheses on `M`
  or `S`;
- derived API: the four textbook finiteness statements after base change.

Source/core/bridge triage:
- `source-facing`: the four clauses of Lemma 10.14.2;
- `core/canonical`: the owner declarations listed above;
- `bridge/view`: the tensor-product models `S ⊗[R] R'` and
  `(S ⊗[R] R') ⊗[S] M`, together with the tensor-symmetry identification relating the textbook
  order of factors to the owner orientation used by mathlib.
-/

section ModuleBaseChange

variable {R S R' M : Type u} [CommRing R] [CommRing S] [CommRing R']
  [Algebra R S] [Algebra R R'] [AddCommGroup M] [Module S M]

/- Lemma 10.14.2 (1): if `M` is a finite `S`-module, then after base change along `R → R'`,
`(S ⊗[R] R') ⊗[S] M` is finite over `S ⊗[R] R'`. This is the canonical theorem
`Module.Finite.base_change`, applied to the `S`-algebra `S ⊗[R] R'`. -/
@[stacks 05G5 "finite module after base change"]
#check @Module.Finite.base_change

/- Lemma 10.14.2 (2): if `M` is a finitely presented `S`-module, then after base change along
`R → R'`, `(S ⊗[R] R') ⊗[S] M` is finitely presented over `S ⊗[R] R'`. Mathlib exposes this as the canonical
tensor-product base-change instance for finitely presented modules. -/
variable [Module.FinitePresentation S M]

@[stacks 05G5 "finitely presented module after base change"]
#check (inferInstance : Module.FinitePresentation (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] M))

end ModuleBaseChange

section AlgebraBaseChange

variable {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
  [Algebra R S] [Algebra R R']

/- Lemma 10.14.2 (3): if `R → S` is of finite type, then the standard base change
`R' → R' ⊗[R] S` is of finite type; via `Algebra.TensorProduct.comm R' S`, this is the textbook
base change `R' → S ⊗[R] R'`. This is the canonical theorem `Algebra.FiniteType.baseChange`. -/
@[stacks 05G5 "finite type after base change"]
#check @Algebra.FiniteType.baseChange

/- Lemma 10.14.2 (4): if `R → S` is of finite presentation, then the standard base change
`R' → R' ⊗[R] S` is of finite presentation; via `Algebra.TensorProduct.comm R' S`, this is the
textbook base change `R' → S ⊗[R] R'`. This is the canonical theorem
`Algebra.FinitePresentation.baseChange`. -/
@[stacks 05G5 "finite presentation after base change"]
#check @Algebra.FinitePresentation.baseChange

end AlgebraBaseChange
