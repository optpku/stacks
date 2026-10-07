module

public import stacks_project.Chap106.Lemma_106_5_2_Deformation
public import stacks_project.Chap106.Lemma_106_5_2_Syntomic
import StacksCheckRecall

/-!
# Deformation of morphism properties of algebraic stacks
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicStack.IsThickening

/- Lemma 106.5.2 (1): in a 2-commutative triangle of thickenings of algebraic
stacks, with Y' ⟶ B' locally of finite type, X' ⟶ B' flat and locally of finite
presentation, and both vertical squares 2-fibre products, f is flat if and only
if f' is flat. -/
@[stacks 0CJC] #check flat_iff

/- Lemma 106.5.2 (2): under the same hypotheses, f is an isomorphism if and only
if f' is an isomorphism. -/
@[stacks 0CJC] #check isIso_iff

/- Lemma 106.5.2 (3): under the same hypotheses, f is an open immersion if and
only if f' is an open immersion. -/
@[stacks 0CJC] #check openImmersion_iff

/- Lemma 106.5.2 (4): under the same hypotheses, f is a monomorphism if and only
if f' is a monomorphism. -/
@[stacks 0CJC] #check mono_iff

/- Lemma 106.5.2 (5): under the same hypotheses, f is locally quasi-finite if and
only if f' is locally quasi-finite. -/
@[stacks 0CJC] #check locallyQuasiFinite_iff

/- Lemma 106.5.2 (6): under the same hypotheses, f is syntomic if and only if f'
is syntomic. -/
@[stacks 0CJC] #check syntomic_iff

/- Lemma 106.5.2 (7): under the same hypotheses, f is smooth if and only if f' is
smooth. -/
@[stacks 0CJC] #check smooth_iff

/- Lemma 106.5.2 (8): under the same hypotheses, f is unramified if and only if
f' is unramified. -/
@[stacks 0CJC] #check unramified_iff

/- Lemma 106.5.2 (9): under the same hypotheses, f is étale if and only if f' is
étale. -/
@[stacks 0CJC] #check etale_iff

/- Lemma 106.5.2 (10): under the same hypotheses, f is finite if and only if f'
is finite. -/
@[stacks 0CJC] #check isFinite_iff
