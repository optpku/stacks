module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.HomotopyCategory.Lift

/-! # Bifunctor Totalization on Homotopy Categories

@stack 0G6E
@stack 064I

Fixing one factor of a bifunctor's tensor-totalization produces an additive functor between
categories of cochain complexes. The bifunctor homotopy API shows that this functor preserves
homotopy, so `Functor.Homotopy.lift` descends it to the corresponding homotopy categories.

## Main declarations

- `HomologicalComplex.instHasBinaryBiproducts` -- homological complexes of any shape over a
  category with binary biproducts again have binary biproducts, computed pointwise.
- `CategoryTheory.Functor.map₂CochainComplex_obj_additive` -- fixing the left factor of
  `tensor.map₂CochainComplex` at `X` gives an additive functor.
- `CategoryTheory.Functor.map₂CochainComplex_flip_obj_additive` -- fixing the right
  factor of `tensor.map₂CochainComplex` at `Y` gives an additive functor.
- `CategoryTheory.Functor.Homotopy.BifunctorTotal.leftFixed` and
  `CategoryTheory.Functor.Homotopy.BifunctorTotal.rightFixed` -- named fixed-factor
  totalization functors on homotopy categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory
open HomologicalComplex

noncomputable section

universe v₁ u₁ v₂ u₂ v₃ u₃

set_option checkBinderAnnotations false

namespace CategoryTheory.Functor

section

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
  [Preadditive 𝒜] [Preadditive ℬ] [Preadditive 𝒞]

variable (tensor : 𝒜 ⥤ ℬ ⥤ 𝒞)
variable [tensor.Additive] [∀ X : 𝒜, (tensor.obj X).Additive]
variable [∀ (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ),
  CochainComplex.HasMapBifunctor X Y tensor]

/-- Fixing the first cochain complex makes the totalized bifunctor additive. -/
@[stacks 0G6E "additivity of left fixed-factor totalization"]
instance map₂CochainComplex_obj_additive (X : CochainComplex 𝒜 ℤ) :
    ((tensor.map₂CochainComplex).obj X).Additive where
  map_add := by
    intro L M f g
    ext j
    apply mapBifunctor.hom_ext
    intro i₁ i₂ h
    change
      ιMapBifunctor X L tensor (up ℤ) i₁ i₂ j h ≫
          (mapBifunctorMap (𝟙 X) (f + g) tensor (up ℤ)).f j =
        ιMapBifunctor X L tensor (up ℤ) i₁ i₂ j h ≫
          ((mapBifunctorMap (𝟙 X) f tensor (up ℤ)).f j +
            (mapBifunctorMap (𝟙 X) g tensor (up ℤ)).f j)
    rw [Preadditive.comp_add]
    simp [Functor.map_add, Preadditive.comp_add]

/-- Fixing the second cochain complex makes the flipped totalized bifunctor additive. -/
@[stacks 0G6E, stacks 064I "additivity of right fixed-factor totalization"]
instance map₂CochainComplex_flip_obj_additive (Y : CochainComplex ℬ ℤ) :
    ((tensor.map₂CochainComplex).flip.obj Y).Additive where
  map_add := by
    intro L M f g
    ext j
    apply mapBifunctor.hom_ext
    intro i₁ i₂ h
    change
      ιMapBifunctor L Y tensor (up ℤ) i₁ i₂ j h ≫
          (mapBifunctorMap (f + g) (𝟙 Y) tensor (up ℤ)).f j =
        ιMapBifunctor L Y tensor (up ℤ) i₁ i₂ j h ≫
          ((mapBifunctorMap f (𝟙 Y) tensor (up ℤ)).f j +
            (mapBifunctorMap g (𝟙 Y) tensor (up ℤ)).f j)
    rw [Preadditive.comp_add]
    simp [Functor.map_add, Preadditive.add_comp]

namespace Homotopy.BifunctorTotal

/-- Fixing the left factor of bifunctor totalization preserves homotopies in the right factor. -/
@[stacks 0G6E "left fixed-factor homotopy preservation"]
theorem leftPreservesHomotopy (X : CochainComplex 𝒜 ℤ) :
    (tensor.map₂CochainComplex.obj X).PreservesHomotopy := sorry

/-- Fixing the right factor of bifunctor totalization preserves homotopies in the left factor. -/
@[stacks 0G6E, stacks 064I "right fixed-factor homotopy preservation"]
theorem rightPreservesHomotopy (Y : CochainComplex ℬ ℤ) :
    (tensor.map₂CochainComplex.flip.obj Y).PreservesHomotopy := sorry

/-- The homotopy-category totalization obtained by fixing the left cochain-complex factor of a
curried additive bifunctor. -/
@[stacks 0G6E "left fixed-factor bifunctor totalization"]
noncomputable def leftFixed (X : CochainComplex 𝒜 ℤ) :
    HomotopyCategory ℬ (up ℤ) ⥤ HomotopyCategory 𝒞 (up ℤ) :=
  Homotopy.lift (tensor.map₂CochainComplex.obj X) (leftPreservesHomotopy tensor X)

/-- The homotopy-category totalization obtained by fixing the right cochain-complex factor of a
curried additive bifunctor. -/
@[stacks 0G6E, stacks 064I "right fixed-factor bifunctor totalization"]
noncomputable def rightFixed (Y : CochainComplex ℬ ℤ) :
    HomotopyCategory 𝒜 (up ℤ) ⥤ HomotopyCategory 𝒞 (up ℤ) :=
  Homotopy.lift (tensor.map₂CochainComplex.flip.obj Y) (rightPreservesHomotopy tensor Y)

/-- The left-fixed descended totalization is additive. -/
@[stacks 0G6E "additivity of the descended left fixed-factor totalization"]
instance leftFixedAdditive (X : CochainComplex 𝒜 ℤ) :
    (leftFixed tensor X).Additive :=
  Homotopy.liftAdditive _ _

/-- The right-fixed descended totalization is additive. -/
@[stacks 0G6E, stacks 064I "additivity of the descended right fixed-factor totalization"]
instance rightFixedAdditive (Y : CochainComplex ℬ ℤ) :
    (rightFixed tensor Y).Additive :=
  Homotopy.liftAdditive _ _

/-- The left-fixed descended totalization commutes with cochain shifts. -/
@[stacks 0G6E "shift compatibility of left fixed-factor totalization"]
noncomputable instance leftFixedCommShift (X : CochainComplex 𝒜 ℤ) :
    (leftFixed tensor X).CommShift ℤ :=
  Homotopy.liftCommShift _ _

/-- The right-fixed descended totalization commutes with cochain shifts. -/
@[stacks 0G6E, stacks 064I "shift compatibility of right fixed-factor totalization"]
noncomputable instance rightFixedCommShift (Y : CochainComplex ℬ ℤ) :
    (rightFixed tensor Y).CommShift ℤ :=
  Homotopy.liftCommShift _ _

/-- The left-fixed descended totalization factors the raw cochain-complex functor. -/
@[stacks 0G6E "left fixed-factor totalization factorization"]
noncomputable def leftFixedFactors (X : CochainComplex 𝒜 ℤ) :
    HomotopyCategory.quotient ℬ (up ℤ) ⋙ leftFixed tensor X ≅
      tensor.map₂CochainComplex.obj X ⋙ HomotopyCategory.quotient 𝒞 (up ℤ) :=
  Homotopy.liftFactors _ (leftPreservesHomotopy tensor X)

/-- The right-fixed descended totalization factors the raw cochain-complex functor. -/
@[stacks 0G6E "right fixed-factor totalization factorization"]
noncomputable def rightFixedFactors (Y : CochainComplex ℬ ℤ) :
    HomotopyCategory.quotient 𝒜 (up ℤ) ⋙ rightFixed tensor Y ≅
      tensor.map₂CochainComplex.flip.obj Y ⋙ HomotopyCategory.quotient 𝒞 (up ℤ) :=
  Homotopy.liftFactors _ (rightPreservesHomotopy tensor Y)

/-- The left-fixed descended totalization computes on quotient objects by raw totalization. -/
@[simp]
theorem leftFixed_obj (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ) :
    (leftFixed tensor X).obj ((HomotopyCategory.quotient ℬ (up ℤ)).obj Y) =
      (HomotopyCategory.quotient 𝒞 (up ℤ)).obj
        ((tensor.map₂CochainComplex.obj X).obj Y) := sorry

/-- The left-fixed descended totalization computes on quotient maps by raw totalization. -/
@[simp]
theorem leftFixed_map (X : CochainComplex 𝒜 ℤ)
    {Y Y' : CochainComplex ℬ ℤ} (f : Y ⟶ Y') :
    (leftFixed tensor X).map ((HomotopyCategory.quotient ℬ (up ℤ)).map f) =
      (HomotopyCategory.quotient 𝒞 (up ℤ)).map
        ((tensor.map₂CochainComplex.obj X).map f) := sorry

/-- The right-fixed descended totalization computes on quotient objects by raw totalization. -/
@[simp]
theorem rightFixed_obj (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ) :
    (rightFixed tensor Y).obj ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj X) =
      (HomotopyCategory.quotient 𝒞 (up ℤ)).obj
        ((tensor.map₂CochainComplex.flip.obj Y).obj X) := sorry

/-- The right-fixed descended totalization computes on quotient maps by raw totalization. -/
@[simp]
theorem rightFixed_map (Y : CochainComplex ℬ ℤ)
    {X X' : CochainComplex 𝒜 ℤ} (f : X ⟶ X') :
    (rightFixed tensor Y).map ((HomotopyCategory.quotient 𝒜 (up ℤ)).map f) =
      (HomotopyCategory.quotient 𝒞 (up ℤ)).map
        ((tensor.map₂CochainComplex.flip.obj Y).map f) := sorry

end Homotopy.BifunctorTotal

variable (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ)




end

end CategoryTheory.Functor
