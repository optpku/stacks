module

public import Mathlib.RingTheory.FinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.6.2

@stack 00F4
-/

/- Lemma 10.6.2 (00F4): the permanence properties of finite type and finite presentation are
exactly the canonical mathlib theorems recalled below. -/

/- Lemma 10.6.2 (1): a composition of ring maps of finite type is again of finite type. This is
the canonical mathlib theorem `RingHom.FiniteType.comp`. -/
@[stacks 00F4 "(1), composition of finite-type maps"]
#check @RingHom.FiniteType.comp

/- Lemma 10.6.2 (2): a composition of ring maps of finite presentation is again of finite
presentation. This is the canonical mathlib theorem `RingHom.FinitePresentation.comp`. -/
@[stacks 00F4 "(2), composition of finitely presented maps"]
#check @RingHom.FinitePresentation.comp

/- Lemma 10.6.2 (3): given ring maps `R → S' → S`, if the composite `R → S` is of finite type,
then `S' → S` is of finite type. This is the canonical mathlib theorem
`RingHom.FiniteType.of_comp_finiteType`. -/
@[stacks 00F4 "(3), finite type of the second map"]
#check @RingHom.FiniteType.of_comp_finiteType

/- Lemma 10.6.2 (4): given ring maps `R → S' → S`, if `R → S` is of finite presentation and
`R → S'` is of finite type, then `S' → S` is of finite presentation. This is the canonical
mathlib theorem `RingHom.FinitePresentation.of_comp_finiteType`. -/
@[stacks 00F4 "(4), finite presentation of the second map"]
#check @RingHom.FinitePresentation.of_comp_finiteType
