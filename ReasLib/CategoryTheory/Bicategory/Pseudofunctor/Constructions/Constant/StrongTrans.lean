module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Constant.Basic

/-!
# Pointwise maps between constant pseudofunctors

Strong transformations and modifications induced pointwise by morphisms and
`2`-morphisms in the target bicategory, together with their hom functor.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Pseudofunctor

universe wJ vJ uJ

variable {B : Type u} [Bicategory.{w, v} B]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]

section ConstantStrongTransImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Naturality in `2`-morphisms for the pointwise map between constant pseudofunctors. -/
private theorem constMap.naturality.naturality {X Y : B} (h : X ⟶ Y) :
    ∀ {a b : J} {k l : a ⟶ b} (η : k ⟶ l),
      (const J X).map₂ η ▷ h ≫ (λ_ h ≪≫ (ρ_ h).symm).hom =
        (λ_ h ≪≫ (ρ_ h).symm).hom ≫ h ◁ (const J Y).map₂ η := sorry
/- Proof strategy: unfold `const`; naturality of the left and right unitors rewrites both
sides to the same composite. -/

/-- Identity coherence for the pointwise map between constant pseudofunctors. -/
private theorem constMap.naturality.id {X Y : B} (h : X ⟶ Y) :
    ∀ a : J,
      (λ_ h ≪≫ (ρ_ h).symm).hom ≫ h ◁ ((const J Y).mapId a).hom =
        ((const J X).mapId a).hom ▷ h ≫ (λ_ h).hom ≫ (ρ_ h).inv := sorry
/- Proof strategy: unfold `const`; expand the identity comparisons and apply the standard
left-right unitor compatibility for `h`. -/

/-- Composition coherence for the pointwise map between constant pseudofunctors. -/
private theorem constMap.naturality.comp {X Y : B} (h : X ⟶ Y) :
    ∀ {a b c : J} (k : a ⟶ b) (l : b ⟶ c),
      (λ_ h ≪≫ (ρ_ h).symm).hom ≫ h ◁ ((const J Y).mapComp k l).hom =
        ((const J X).mapComp k l).hom ▷ h ≫
          (α_ ((const J X).map k) ((const J X).map l) h).hom ≫
          (const J X).map k ◁ (λ_ h ≪≫ (ρ_ h).symm).hom ≫
          (α_ ((const J X).map k) h ((const J Y).map l)).inv ≫
          (λ_ h ≪≫ (ρ_ h).symm).hom ▷ (const J Y).map l ≫
          (α_ h ((const J Y).map k) ((const J Y).map l)).hom := sorry
/- Proof strategy: unfold `const`; all diagram arrows become identities, and the pentagon
and triangle coherence equations identify the two composites. -/

end Implementation

variable (J) in
/-- The strong transformation induced pointwise by `h` between constant pseudofunctors. -/
def constMap {X Y : B} (h : X ⟶ Y) : const J X ⟶ const J Y where
  app _ := h
  naturality _ := λ_ h ≪≫ (ρ_ h).symm
  naturality_naturality := Implementation.constMap.naturality.naturality h
  naturality_id := Implementation.constMap.naturality.id h
  naturality_comp := Implementation.constMap.naturality.comp h

/-- The component of a pointwise map between constant pseudofunctors is the original
`1`-morphism. -/
@[simp]
theorem constMap.app {X Y : B} (h : X ⟶ Y) (a : J) :
    (constMap J h).app a = h := sorry

/-- The naturality comparison of a pointwise map between constant pseudofunctors is the
canonical composite of unitors. -/
@[simp]
theorem constMap.naturality {X Y : B} (h : X ⟶ Y)
    {a b : J} (f : a ⟶ b) :
    (constMap J h).naturality f = λ_ h ≪≫ (ρ_ h).symm := sorry

namespace Implementation

variable (J) in
/-- Modification naturality for a pointwise `2`-morphism between constant maps. -/
private theorem constMap₂.naturality {X Y : B} {h k : X ⟶ Y} (η : h ⟶ k) :
    ∀ {a b : J} (l : a ⟶ b),
      (const J X).map l ◁ η ≫ ((constMap J k).naturality l).hom =
        ((constMap J h).naturality l).hom ≫ η ▷ (const J Y).map l := sorry
/- Proof strategy: unfold `constMap` and `const`; use naturality of `η` with both unitors,
then normalize whiskering by bicategory coherence. -/

end Implementation

variable (J) in
/-- The pointwise modification induced by `η` between constant maps. -/
def constMap₂ {X Y : B} {h k : X ⟶ Y} (η : h ⟶ k) :
    constMap J h ⟶ constMap J k where
  as.app _ := η
  as.naturality := Implementation.constMap₂.naturality J η

/-- The component of a pointwise modification between constant maps is the original
`2`-morphism. -/
@[simp]
theorem constMap₂.app {X Y : B} {h k : X ⟶ Y} (η : h ⟶ k) (a : J) :
    (constMap₂ J η).as.app a = η := sorry

variable (J) in
/-- Pointwise constant modifications preserve identity `2`-morphisms. -/
theorem constMap₂.id {X Y : B} (h : X ⟶ Y) :
    constMap₂ J (𝟙 h) = 𝟙 (constMap J h) := sorry
/- Proof strategy: apply modification extensionality; each component is the identity
`2`-morphism by definition. -/

variable (J) in
/-- Pointwise constant modifications preserve vertical composition. -/
theorem constMap₂.comp {X Y : B} {h k l : X ⟶ Y}
    (η : h ⟶ k) (θ : k ⟶ l) :
    constMap₂ J (η ≫ θ) = constMap₂ J η ≫ constMap₂ J θ := sorry
/- Proof strategy: apply modification extensionality; componentwise both sides are `η ≫ θ`. -/

variable (J) in
/-- The hom functor giving the pointwise action of the varying constant diagram. -/
def constMapFunctor (X Y : B) :
    (X ⟶ Y) ⥤ (const J X ⟶ const J Y) where
  obj := constMap J
  map := constMap₂ J
  map_id := constMap₂.id J
  map_comp := constMap₂.comp J

variable (J) in
/-- The object action of the hom functor for varying constant diagrams is `constMap`. -/
@[simp]
theorem constMapFunctor.obj {X Y : B} (h : X ⟶ Y) :
    (constMapFunctor J X Y).obj h = constMap J h := sorry

variable (J) in
/-- The morphism action of the hom functor for varying constant diagrams is `constMap₂`. -/
@[simp]
theorem constMapFunctor.map {X Y : B} {h k : X ⟶ Y} (η : h ⟶ k) :
    (constMapFunctor J X Y).map η = constMap₂ J η := sorry

end ConstantStrongTransImplementation

end Pseudofunctor

end CategoryTheory
