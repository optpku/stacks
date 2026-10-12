/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Algebraic.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.8.11:
- primary domain: algebraic field extensions and their endomorphisms;
- sampled owner declarations:
  `Algebra.IsAlgebraic.algHom_bijective`,
  `Algebra.IsAlgebraic.algEquivEquivAlgHom`,
  `AlgEquiv.ofBijective`,
  `AlgEquiv.toAlgHom`;
- best owner abstraction: the extension-level owner theorem
  `Algebra.IsAlgebraic.algHom_bijective`, which directly states bijectivity of an
  `F`-algebra endomorphism of an algebraic field extension;
- primitive data: the algebraic field extension `F ⟶ E` and an endomorphism `f : E →ₐ[F] E`;
- derived API: turning that bijective endomorphism into an automorphism via `AlgEquiv.ofBijective`,
  or packaging all such endomorphisms as equivalences via
  `Algebra.IsAlgebraic.algEquivEquivAlgHom`.

Source/core/bridge triage:
- `source-facing`: the textbook fact that an endomorphism of an algebraic field extension is an
  automorphism;
- `core/canonical`: `Algebra.IsAlgebraic.algHom_bijective`;
- `bridge/view`: `AlgEquiv.ofBijective` and `Algebra.IsAlgebraic.algEquivEquivAlgHom`, which
  convert the bijectivity statement into the automorphism viewpoint.

This file should therefore remain check-only: the source lemma is owned canonically by the
bijection theorem `Algebra.IsAlgebraic.algHom_bijective`, and the automorphism viewpoint is
already provided upstream by `Algebra.IsAlgebraic.algEquivEquivAlgHom`. Any local theorem or
abbrev would only duplicate owner-level API. -/

/- Lemma 9.8.11: for an algebraic field extension `E/F`, any `F`-algebra endomorphism
`f : E →ₐ[F] E` is bijective, hence an `F`-algebra automorphism. This is the canonical mathlib
theorem `Algebra.IsAlgebraic.algHom_bijective`. -/
@[stacks 0BMD]
#check Algebra.IsAlgebraic.algHom_bijective

/- Companion check: the automorphism viewpoint is already packaged canonically by the
multiplicative equivalence between `F`-algebra automorphisms of `E` and `F`-algebra endomorphisms
of `E`, namely `Algebra.IsAlgebraic.algEquivEquivAlgHom`. -/
#check Algebra.IsAlgebraic.algEquivEquivAlgHom
