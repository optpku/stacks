/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Constant pseudofunctors

The shape-independent constant pseudofunctor and its object, morphism, cell,
and coherence comparison computations.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

universe wJ vJ uJ

variable {B : Type u} [Bicategory.{w, v} B]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]

section ConstantImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The implementation-level prelax core of the constant pseudofunctor. -/
private def const.prelax (J : Type uJ) [Bicategory.{wJ, vJ} J] (X : B) :
    PrelaxFunctor J B :=
  PrelaxFunctor.mkOfHomFunctors (fun _ ↦ X) fun a b ↦
    (Functor.const (a ⟶ b)).obj (𝟙 X)

/-- Constant maps preserve left whiskering up to the chosen unit comparison. -/
private theorem const.map₂.whiskerLeft
    (J : Type uJ) [Bicategory.{wJ, vJ} J] (X : B) :
    ∀ {a b c : J} (h : a ⟶ b) {k l : b ⟶ c} (η : k ⟶ l),
    (const.prelax J X).map₂ (h ◁ η) =
        (λ_ (𝟙 X)).inv ≫ (const.prelax J X).map h ◁
          (const.prelax J X).map₂ η ≫ (λ_ (𝟙 X)).hom := sorry
/- Proof strategy: unfold `const.prelax`; both sides reduce to unitor naturality and the
triangle coherence law for `𝟙 X`. -/

/-- Constant maps preserve right whiskering up to the chosen unit comparison. -/
private theorem const.map₂.whiskerRight
    (J : Type uJ) [Bicategory.{wJ, vJ} J] (X : B) :
    ∀ {a b c : J} {h k : a ⟶ b} (η : h ⟶ k) (l : b ⟶ c),
    (const.prelax J X).map₂ (η ▷ l) =
        (λ_ (𝟙 X)).inv ≫ (const.prelax J X).map₂ η ▷
          (const.prelax J X).map l ≫ (λ_ (𝟙 X)).hom := sorry
/- Proof strategy: unfold `const.prelax`; both sides reduce to unitor naturality and the
triangle coherence law for `𝟙 X`. -/

/-- Constant maps preserve the associator up to the chosen unit comparison. -/
private theorem const.map₂.associator
    (J : Type uJ) [Bicategory.{wJ, vJ} J] (X : B) :
    ∀ {a b c d : J} (h : a ⟶ b) (k : b ⟶ c) (l : c ⟶ d),
    (const.prelax J X).map₂ (α_ h k l).hom =
        (λ_ (𝟙 X)).inv ≫ (λ_ (𝟙 X)).inv ▷ (const.prelax J X).map l ≫
          (α_ ((const.prelax J X).map h) ((const.prelax J X).map k)
            ((const.prelax J X).map l)).hom ≫
          (const.prelax J X).map h ◁ (λ_ (𝟙 X)).hom ≫ (λ_ (𝟙 X)).hom := sorry
/- Proof strategy: unfold `const.prelax`; all mapped arrows are identities, and the goal is
the standard pentagon-triangle coherence identity. -/

/-- Constant maps preserve the left unitor up to the chosen unit comparison. -/
private theorem const.map₂.leftUnitor
    (J : Type uJ) [Bicategory.{wJ, vJ} J] (X : B) :
    ∀ {a b : J} (h : a ⟶ b),
    (const.prelax J X).map₂ (λ_ h).hom =
        (λ_ (𝟙 X)).inv ≫ (𝟙 ((const.prelax J X).map (𝟙 a))) ▷
          (const.prelax J X).map h ≫ (λ_ ((const.prelax J X).map h)).hom := sorry
/- Proof strategy: unfold `const.prelax`; normalize mapped identities and apply the left-unitor
triangle coherence identity. -/

/-- Constant maps preserve the right unitor up to the chosen unit comparison. -/
private theorem const.map₂.rightUnitor
    (J : Type uJ) [Bicategory.{wJ, vJ} J] (X : B) :
    ∀ {a b : J} (h : a ⟶ b),
    (const.prelax J X).map₂ (ρ_ h).hom =
        (λ_ (𝟙 X)).inv ≫ (const.prelax J X).map h ◁
          (𝟙 ((const.prelax J X).map (𝟙 b))) ≫
          (ρ_ ((const.prelax J X).map h)).hom := sorry
/- Proof strategy: unfold `const.prelax`; normalize mapped identities and apply the right-unitor
triangle coherence identity. -/

end Implementation

/-- The constant pseudofunctor at `X`. Its object, `1`-morphism, and `2`-morphism actions are
definitionally constant; its proof-only coherence fields are private implementation details. -/
def const (J : Type uJ) [Bicategory.{wJ, vJ} J] (X : B) : J ⥤ᵖ B where
  toPrelaxFunctor := Implementation.const.prelax J X
  mapId _ := Iso.refl _
  mapComp _ _ := (λ_ (𝟙 X)).symm
  map₂_whisker_left := Implementation.const.map₂.whiskerLeft J X
  map₂_whisker_right := Implementation.const.map₂.whiskerRight J X
  map₂_associator := Implementation.const.map₂.associator J X
  map₂_left_unitor := Implementation.const.map₂.leftUnitor J X
  map₂_right_unitor := Implementation.const.map₂.rightUnitor J X

/-- A constant pseudofunctor has value `X` at every object. -/
@[simp]
theorem const.obj (X : B) (a : J) :
    (const J X).obj a = X := sorry
/- Proof strategy: unfold `const` and project the object field of its constant prelax core. -/

/-- A constant pseudofunctor sends every `1`-morphism to `𝟙 X`. -/
@[simp]
theorem const.map (X : B)
    {a b : J} (f : a ⟶ b) :
    (const J X).map f = 𝟙 X := sorry
/- Proof strategy: unfold `const` and project the object map of the constant hom functor. -/

/-- A constant pseudofunctor sends every `2`-morphism to `𝟙 (𝟙 X)`. -/
@[simp]
theorem const.map₂ (X : B)
    {a b : J} {f g : a ⟶ b} (η : f ⟶ g) :
    (const J X).map₂ η = 𝟙 (𝟙 X) := sorry
/- Proof strategy: unfold `const` and project the morphism map of the constant hom functor. -/

/-- The hom functor of a constant pseudofunctor is the corresponding constant functor at
`𝟙 X`. -/
@[simp]
theorem const.mapFunctor (X : B) (a b : J) :
    (const J X).mapFunctor a b = (Functor.const (a ⟶ b)).obj (𝟙 X) := sorry

/-- The identity comparison of a constant pseudofunctor is reflexivity. -/
@[simp]
theorem const.mapId (X : B) (a : J) :
    (const J X).mapId a = Iso.refl (𝟙 X) := sorry
/- Proof strategy: project the `mapId` field of `const`. -/

/-- The composition comparison of a constant pseudofunctor is the inverse left unitor. -/
@[simp]
theorem const.mapComp (X : B)
    {a b c : J} (f : a ⟶ b) (g : b ⟶ c) :
    (const J X).mapComp f g = (λ_ (𝟙 X)).symm := sorry
/- Proof strategy: project the `mapComp` field of `const`. -/

end ConstantImplementation

end Pseudofunctor

end CategoryTheory
