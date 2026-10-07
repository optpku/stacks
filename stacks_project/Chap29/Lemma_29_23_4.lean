module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import StacksCheckRecall

/-!
# Lemma 29.23.4

The structure morphism of a scheme over a field is universally open.

@stack 0383
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k]
variable (X : Over (Spec (CommRingCat.of k)))

/- Lemma 29.23.4: The structure morphism of a scheme over a field is universally open. -/
@[stacks 0383] #check
  (AlgebraicGeometry.instUniversallyOpenOfIsIntegralOfSubsingletonCarrierCarrierCommRingCat X.hom :
    AlgebraicGeometry.UniversallyOpen X.hom)
