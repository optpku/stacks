module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap76.Definition_76_9_1_Arrow
public import stacks_project.Chap76.Definition_76_12_1_Neighbourhood

/-!
# Universal-property glue for infinitesimal neighbourhoods of immersions

A commutative square over an immersion of algebraic spaces induces a square
against the infinitesimal neighbourhood, and that neighbourhood is a thickening
over the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom.InfinitesimalNeighbourhood

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}

/-- A commutative square over an immersion induces a commutative square against
the canonical map from its `n`th infinitesimal neighbourhood to the ambient
space. -/
theorem factorizationCommSq {T T' : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
    (n : ℕ) (j : T ⟶ T') (a : T ⟶ Z) (b : T' ⟶ X) (sq : CommSq a j i b) :
    CommSq (a ≫ fromSource i n) j (toAmbient i n) b :=
  sorry

/-- The infinitesimal neighbourhood of an immersion, as a thickening over the
ambient algebraic space. -/
def over (i : Z ⟶ X) [IsImmersion i] (n : ℕ) : Thickening.Over X :=
  MorphismProperty.Arrow.mk
    (Over.homMk (fromSource i n) (fromSource_toAmbient i n) :
      Over.mk i ⟶ Over.mk (toAmbient i n))
    (inferInstance : IsThickening (fromSource i n))

/-- The source of `over i n` is the original immersion, viewed over `X`. -/
theorem over_left (i : Z ⟶ X) [IsImmersion i] (n : ℕ) :
    (over i n).left = Over.mk i :=
  sorry

/-- The target of `over i n` is the infinitesimal neighbourhood, viewed over `X`. -/
theorem over_right (i : Z ⟶ X) [IsImmersion i] (n : ℕ) :
    (over i n).right = Over.mk (toAmbient i n) :=
  sorry

/-- The underlying morphism of `over i n` is the coborder factorization through
the infinitesimal neighbourhood. -/
theorem over_hom (i : Z ⟶ X) [IsImmersion i] (n : ℕ) :
    (over i n).hom =
      (Over.homMk (fromSource i n) (fromSource_toAmbient i n) :
        Over.mk i ⟶ Over.mk (toAmbient i n)) :=
  sorry

end Hom.InfinitesimalNeighbourhood

end AlgebraicGeometry.AlgebraicSpace
