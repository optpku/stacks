module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.LinearAlgebra.Dual.Defs

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

variable (k : Type w) (T : Type u) [Field k] [Category.{v} T] [Preadditive T] [Linear k T]

/-- A Serre functor on a `k`-linear category consists of a linear autoequivalence together
with a bifunctorial identification of each Hom space with the dual of the corresponding
Hom space into the image under the autoequivalence. -/
structure SerreFunctor where
  /-- The underlying autoequivalence. -/
  toEquivalence : T ≌ T
  /-- The forward functor of the autoequivalence is `k`-linear. -/
  linear : toEquivalence.functor.Linear k
  /-- The linear duality equivalence on Hom spaces. -/
  pairing : ∀ X Y : T,
    (X ⟶ Y) ≃ₗ[k] Module.Dual k (Y ⟶ toEquivalence.functor.obj X)
  /-- Naturality of the pairing contravariantly in its first object. -/
  naturality_left : ∀ ⦃X X' Y : T⦄ (f : X' ⟶ X) (g : X ⟶ Y)
      (h : Y ⟶ toEquivalence.functor.obj X'),
    pairing X' Y (f ≫ g) h =
      pairing X Y g (h ≫ toEquivalence.functor.map f)
  /-- Naturality of the pairing covariantly in its second object. -/
  naturality_right : ∀ ⦃X Y Y' : T⦄ (g : X ⟶ Y) (f : Y ⟶ Y')
      (h : Y' ⟶ toEquivalence.functor.obj X),
    pairing X Y' (g ≫ f) h = pairing X Y g (f ≫ h)

namespace SerreFunctor

variable {k T}

/-- Construct a Serre functor from an autoequivalence, a Hom-duality pairing, and its
linearity and naturality laws. -/
def ofEquivalence (S : T ≌ T) (hlinear : S.functor.Linear k)
    (c : ∀ X Y : T, (X ⟶ Y) ≃ₗ[k] Module.Dual k (Y ⟶ S.functor.obj X))
    (hnatural_left : ∀ ⦃X X' Y : T⦄ (f : X' ⟶ X) (g : X ⟶ Y)
      (h : Y ⟶ S.functor.obj X'),
      c X' Y (f ≫ g) h = c X Y g (h ≫ S.functor.map f))
    (hnatural_right : ∀ ⦃X Y Y' : T⦄ (g : X ⟶ Y) (f : Y ⟶ Y')
      (h : Y' ⟶ S.functor.obj X),
      c X Y' (g ≫ f) h = c X Y g (f ≫ h)) : SerreFunctor k T :=
  { toEquivalence := S
    linear := hlinear
    pairing := c
    naturality_left := hnatural_left
    naturality_right := hnatural_right }

/-- The underlying equivalence of `ofEquivalence` is the supplied equivalence. -/
theorem ofEquivalence_toEquivalence (S : T ≌ T) (hlinear : S.functor.Linear k)
    (c : ∀ X Y : T, (X ⟶ Y) ≃ₗ[k] Module.Dual k (Y ⟶ S.functor.obj X))
    (hnatural_left : ∀ ⦃X X' Y : T⦄ (f : X' ⟶ X) (g : X ⟶ Y)
      (h : Y ⟶ S.functor.obj X'),
      c X' Y (f ≫ g) h = c X Y g (h ≫ S.functor.map f))
    (hnatural_right : ∀ ⦃X Y Y' : T⦄ (g : X ⟶ Y) (f : Y ⟶ Y')
      (h : Y' ⟶ S.functor.obj X),
      c X Y' (g ≫ f) h = c X Y g (f ≫ h)) :
    (ofEquivalence S hlinear c hnatural_left hnatural_right).toEquivalence = S := sorry

/-- The pairing of `ofEquivalence` is the supplied Hom-duality equivalence. -/
theorem ofEquivalence_pairing (S : T ≌ T) (hlinear : S.functor.Linear k)
    (c : ∀ X Y : T, (X ⟶ Y) ≃ₗ[k] Module.Dual k (Y ⟶ S.functor.obj X))
    (hnatural_left : ∀ ⦃X X' Y : T⦄ (f : X' ⟶ X) (g : X ⟶ Y)
      (h : Y ⟶ S.functor.obj X'),
      c X' Y (f ≫ g) h = c X Y g (h ≫ S.functor.map f))
    (hnatural_right : ∀ ⦃X Y Y' : T⦄ (g : X ⟶ Y) (f : Y ⟶ Y')
      (h : Y' ⟶ S.functor.obj X),
      c X Y' (g ≫ f) h = c X Y g (f ≫ h)) (X Y : T) :
    (ofEquivalence S hlinear c hnatural_left hnatural_right).pairing X Y = c X Y := sorry

/-- The two naturality equations are the defining functoriality conditions for the
Hom-duality pairing of a Serre functor. -/
theorem naturality_spec (S : SerreFunctor k T) :
    (∀ ⦃X X' Y : T⦄ (f : X' ⟶ X) (g : X ⟶ Y)
      (h : Y ⟶ S.toEquivalence.functor.obj X'),
      S.pairing X' Y (f ≫ g) h =
        S.pairing X Y g (h ≫ S.toEquivalence.functor.map f)) ∧
    (∀ ⦃X Y Y' : T⦄ (g : X ⟶ Y) (f : Y ⟶ Y')
      (h : Y' ⟶ S.toEquivalence.functor.obj X),
      S.pairing X Y' (g ≫ f) h = S.pairing X Y g (f ≫ h)) := sorry

end SerreFunctor

end CategoryTheory

end
