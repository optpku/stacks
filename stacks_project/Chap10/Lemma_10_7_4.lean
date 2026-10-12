/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.7.4

@stack 0D46
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.7.4 (1): a finite ring map `φ : R → S` is of finite type. This is exactly the
canonical mathlib theorem `RingHom.Finite.to_finiteType`. -/
@[stacks 0D46 "(1), finite maps are of finite type"]
#check @RingHom.Finite.to_finiteType

/- Lemma 10.7.4 (2), owner abstraction: if an `R`-algebra `S` is finitely presented as an
`R`-module, then `S` is finitely presented as an `R`-algebra. -/
@[stacks 0D46 "(2), module-finite-presentation owner"]
#check @Algebra.FinitePresentation.of_finitePresentation

/- Lemma 10.7.4 (2), `bridge/view` layer: the ring-map formulation is obtained from the owner
abstraction `Algebra.FinitePresentation` via the canonical equivalence for `algebraMap`. -/
@[stacks 0D46 "(2), ring-map bridge"]
#check @RingHom.finitePresentation_algebraMap
