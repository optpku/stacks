/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Derivation.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.131.1

@stack 00RN
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain triage:
- primary domain: commutative-algebra derivations and their universal role in Kähler
  differentials;
- sampled owner declarations: `Derivation`, `Derivation.leibniz`,
  `KaehlerDifferential.D`, `KaehlerDifferential.linearMapEquivDerivation`;
- best owner abstraction: `Derivation`, the ambient owner of an `R`-derivation from an
  `R`-algebra `S` to an `S`-module `M`;
- layer: `core/canonical`, since Definition 10.131.1 is only recalling the standard owner notion;
- primitive data: an `R`-algebra `S`, an `S`-module `M`, and the additive/Leibniz axioms;
- derived API: the underlying linear map, Leibniz lemmas, and the universal derivation
  `KaehlerDifferential.D`.
-/

/- Definition 10.131.1 is a `core/canonical` recall item: the source notion of an `R`-derivation
from an `R`-algebra `S` to an `S`-module `M` is already owned upstream by `Derivation`, so this
file should recall that owner directly rather than restating its fields or introducing a parallel
wrapper. -/
@[stacks 00RN]
#check @Derivation
