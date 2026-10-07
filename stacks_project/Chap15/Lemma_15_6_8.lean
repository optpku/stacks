module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Flat
import StacksCheckRecall

/-!
# Lemma 15.6.8

The shared owner explicitly restricts the module base-change and fibre-product functors to the
flat full subcategories.  The three source clauses are the flatness, reconstruction, and
equivalence propositions below.

@stack 0D2I
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

@[stacks 0D2I "flat module object property"]
#check (ModuleCat.flat S.Bprime)
@[stacks 0D2I "category of flat modules"]
#check (ModuleCat.Flat S.Bprime)
@[stacks 0D2I "componentwise flat pullback modules"]
#check (ModuleCat.Pullback.Flat.property S)
@[stacks 0D2I "flat pullback module category"]
#check (ModuleCat.Pullback.Flat.Category S)
@[stacks 0D2I "flat pullback base-change functor"]
#check (ModuleCat.Pullback.Flat.baseChangeFunctor S)
@[stacks 0D2I "flat fibre-product module functor"]
#check (ModuleCat.Pullback.Flat.rightAdjointFunctor S)

/- Lemma 15.6.8 (1): a pullback triple with flat components has a flat fibre-product module. -/
@[stacks 0D2I "(1), flat fibre-product module"]
#check (ModuleCat.Pullback.Flat.rightAdjoint_mem S)

/- Lemma 15.6.8 (2): a flat module over the pullback ring is reconstructed by the adjunction
unit from its two scalar extensions. -/
@[stacks 0D2I "(2), flat module reconstruction"]
#check (ModuleCat.Pullback.Flat.unit_isIso S)

/- Lemma 15.6.8 (3): base change is an equivalence between flat modules over the pullback ring
and pullback triples with flat components. -/
@[stacks 0D2I "(3), equivalence on flat modules"]
#check (ModuleCat.Pullback.Flat.baseChangeFunctor_isEquivalence S)

#print axioms CategoryTheory.ModuleCat.Pullback.Flat.baseChangeFunctor
#print axioms CategoryTheory.ModuleCat.Pullback.Flat.rightAdjointFunctor
