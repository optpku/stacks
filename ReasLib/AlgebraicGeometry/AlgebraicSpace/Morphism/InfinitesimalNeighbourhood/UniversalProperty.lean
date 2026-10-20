module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.InfinitesimalNeighbourhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Arrow

/-!
# Universal property of infinitesimal neighbourhoods of algebraic spaces

The canonical infinitesimal neighbourhood of an immersion is universal among
compatible thickenings of the corresponding order over the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

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

/-- For `1 ≤ n`, every `n`th-order thickening in a commutative square over an
immersion admits a unique lift to its canonical `n`th infinitesimal neighbourhood. -/
theorem existsUnique_lift {S : Scheme.{u}} {Z X T T' : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] (n : ℕ) (hn : 1 ≤ n) (j : T ⟶ T')
    [IsNthOrderThickening n j] (a : T ⟶ Z) (b : T' ⟶ X) (sq : CommSq a j i b) :
    Nonempty (Unique (factorizationCommSq i n j a b sq).LiftStruct) :=
  sorry

/-- Every first-order thickening in a commutative square over an immersion
admits a unique lift to its canonical first-order infinitesimal neighbourhood. -/
theorem existsUnique_lift_firstOrder {S : Scheme.{u}} {Z X T T' : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] (j : T ⟶ T') [IsFirstOrderThickening j]
    (a : T ⟶ Z) (b : T' ⟶ X) (sq : CommSq a j i b) :
    Nonempty (Unique (factorizationCommSq i 1 j a b sq).LiftStruct) :=
  sorry

/-- A first-order or finite-order thickening square over `X` admits a unique
morphism of thickenings over `X` to the infinitesimal neighbourhood, with
prescribed map on the closed subspace. -/
theorem existsUnique_hom {S : Scheme.{u}} {Z X T T' : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] (n : ℕ) (hn : 1 ≤ n) (j : T ⟶ T')
    [IsNthOrderThickening n j] (a : T ⟶ Z) (b : T' ⟶ X) (sq : CommSq a j i b) :
    ∃! g : Thickening.of j ⟶ Thickening.of (fromSource i n),
      g.left = a ∧ g.right ≫ toAmbient i n = b :=
  sorry

end Hom.InfinitesimalNeighbourhood

end AlgebraicGeometry.AlgebraicSpace
