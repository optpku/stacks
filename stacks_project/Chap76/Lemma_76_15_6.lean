module

public import stacks_project.Chap76.Lemma_76_14_4_FormallyUnramified
public import stacks_project.Chap76.«76_15_0_1_Universal»
public import stacks_project.Chap76.Definition_76_12_1_Neighbourhood
public import stacks_project.Chap76.Lemma_76_12_3
import StacksCheckRecall

/-!
# Immersions of algebraic spaces and universal first-order thickenings

An immersion of algebraic spaces is formally unramified. Its universal
first-order thickening over the ambient space is the first-order infinitesimal
neighbourhood, and the two conormal sheaves agree.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.15.6 (1): Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `S`. Then `i` is formally unramified. -/
@[stacks 0608, instance]
instance formallyUnramified_of_isImmersion {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] : FormallyUnramified i :=
  sorry

namespace Hom.InfinitesimalNeighbourhood

/-- Lemma 76.15.6 (2): Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `S`. The universal first-order thickening of `Z` over `X`
is the first-order infinitesimal neighbourhood of `Z` in `X` of
Definition 76.12.1. -/
@[stacks 0608, instance]
instance fromSource_isUniversalFirstOrder {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] :
    IsUniversalFirstOrder (fromSource i 1) (toAmbient i 1) :=
  sorry

end Hom.InfinitesimalNeighbourhood

/- Lemma 76.15.6 (3): Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `S`. The conormal sheaf of `i` in the sense of
Definition 76.5.1 agrees with the conormal sheaf of `i` in the sense of
Definition 76.15.5. -/
@[stacks 0608] #check
  (Hom.InfinitesimalNeighbourhood.conormalComparison_isIso :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
      IsIso (Hom.InfinitesimalNeighbourhood.conormalComparison i))

end AlgebraicGeometry.AlgebraicSpace
