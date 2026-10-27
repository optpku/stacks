/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.WeakInverse.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict inverses of strict pseudofunctors

This module owns the equality-level inverse certificate for strict pseudofunctors.
It is deliberately independent of any particular bicategory of stacks.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.StrictPseudofunctor

/-- An equality-level certificate that two strict pseudofunctors are mutually inverse on
objects, `1`-morphisms, and `2`-morphisms.

This strict presentation is useful when a construction is computationally inverse.  It is
stronger than a bicategorical equivalence, whose general owner uses strong transformations and
invertible modifications. -/
structure IsStrictInverse
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    (F : StrictPseudofunctor B D) (G : StrictPseudofunctor D B) : Prop where
  /-- The composite `G.obj ∘ F.obj` is strictly the identity on objects. -/
  left_obj : ∀ X : B, G.obj (F.obj X) = X
  /-- The composite `G.map ∘ F.map` is heterogeneously the identity on `1`-morphisms. -/
  left_map : ∀ ⦃X Y : B⦄ (f : X ⟶ Y), G.map (F.map f) ≍ f
  /-- The composite `G.map₂ ∘ F.map₂` is heterogeneously the identity on `2`-morphisms. -/
  left_map₂ : ∀ ⦃X Y : B⦄ {f g : X ⟶ Y} (η : f ⟶ g), G.map₂ (F.map₂ η) ≍ η
  /-- The composite `F.obj ∘ G.obj` is strictly the identity on objects. -/
  right_obj : ∀ X : D, F.obj (G.obj X) = X
  /-- The composite `F.map ∘ G.map` is heterogeneously the identity on `1`-morphisms. -/
  right_map : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), F.map (G.map f) ≍ f
  /-- The composite `F.map₂ ∘ G.map₂` is heterogeneously the identity on `2`-morphisms. -/
  right_map₂ : ∀ ⦃X Y : D⦄ {f g : X ⟶ Y} (η : f ⟶ g), F.map₂ (G.map₂ η) ≍ η

/-- Reversing an equality-level inverse certificate exchanges the two strict
pseudofunctors. -/
theorem IsStrictInverse.symm
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    {F : StrictPseudofunctor B D} {G : StrictPseudofunctor D B}
    (h : IsStrictInverse F G) : IsStrictInverse G F := by
  exact ⟨h.right_obj, h.right_map, h.right_map₂, h.left_obj, h.left_map, h.left_map₂⟩

/-- Strict pseudofunctors preserve heterogeneous equality after transporting endpoints. -/
private theorem mapHEq
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    (F : StrictPseudofunctor B D)
    {a a' b b' : B} (p : a' = a) (q : b' = b)
    {f' : a' ⟶ b'} {f : a ⟶ b} (hf : f' ≍ f) : F.map f' ≍ F.map f := by
  subst a
  subst b
  cases hf
  rfl

/-- The analogous transport rule for `2`-morphisms. -/
private theorem map₂HEq
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    (F : StrictPseudofunctor B D)
    {a a' b b' : B} (p : a' = a) (q : b' = b)
    {f' g' : a' ⟶ b'} {f g : a ⟶ b} (hf : f' ≍ f) (hg : g' ≍ g)
    {η' : f' ⟶ g'} {η : f ⟶ g} (hη : η' ≍ η) : F.map₂ η' ≍ F.map₂ η := by
  subst a
  subst b
  cases hf
  cases hg
  cases hη
  rfl

/-- Compose equality-level strict inverse certificates. The inverse of the composite is the
reverse composite of the selected strict inverses. -/
theorem IsStrictInverse.comp
    {A : Type u₁} [Bicategory.{w₁, v₁} A]
    {B : Type u₂} [Bicategory.{w₂, v₂} B]
    {C : Type u₃} [Bicategory.{w₃, v₃} C]
    {F : StrictPseudofunctor A B} {G : StrictPseudofunctor B A}
    {H : StrictPseudofunctor B C} {K : StrictPseudofunctor C B}
    (hFG : IsStrictInverse F G) (hHK : IsStrictInverse H K) :
    IsStrictInverse (F.comp H) (K.comp G) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X
    exact (congrArg G.obj (hHK.left_obj (F.obj X))).trans (hFG.left_obj X)
  · intro X Y f
    exact (mapHEq G (hHK.left_obj _) (hHK.left_obj _)
      (hHK.left_map (F.map f))).trans (hFG.left_map f)
  · intro X Y f g η
    exact (map₂HEq G (hHK.left_obj _) (hHK.left_obj _)
      (hHK.left_map _) (hHK.left_map _) (hHK.left_map₂ (F.map₂ η))).trans
      (hFG.left_map₂ η)
  · intro X
    exact (congrArg H.obj (hFG.right_obj (K.obj X))).trans (hHK.right_obj X)
  · intro X Y f
    exact (mapHEq H (hFG.right_obj _) (hFG.right_obj _)
      (hFG.right_map (K.map f))).trans (hHK.right_map f)
  · intro X Y f g η
    exact (map₂HEq H (hFG.right_obj _) (hFG.right_obj _)
      (hFG.right_map _) (hFG.right_map _) (hFG.right_map₂ (K.map₂ η))).trans
      (hHK.right_map₂ η)

/-- A strict pseudofunctor admitting an equality-level strict inverse is a biequivalence after
forgetting strictness. -/
theorem IsStrictInverse.leftIsBiequivalence
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    {F : StrictPseudofunctor B D} {G : StrictPseudofunctor D B}
    (h : IsStrictInverse F G) :
    Pseudofunctor.IsBiequivalence F.toPseudofunctor := by
  have transportMap : ∀ {a a' b b' : B} (p : a' = a) (q : b' = b) (f' : a' ⟶ b'),
      ∃ f : a ⟶ b, f' ≍ f := by
    intro a a' b b' p q f'
    subst a
    subst b
    exact ⟨f', HEq.rfl⟩
  have transportMap₂ : ∀ {a a' b b' : B} (p : a' = a) (q : b' = b)
      {f' g' : a' ⟶ b'} {f g : a ⟶ b} (hf : f' ≍ f) (hg : g' ≍ g)
      (η' : f' ⟶ g'), ∃ η : f ⟶ g, η' ≍ η := by
    intro a a' b b' p q f' g' f g hf hg η'
    subst a
    subst b
    cases hf
    cases hg
    exact ⟨η', HEq.rfl⟩
  refine { mapFunctor_isEquivalence := ?_, mem_essImage := ?_ }
  · intro X Y
    refine { faithful := ⟨?_⟩, full := ⟨?_⟩, essSurj := ⟨?_⟩ }
    · intro f g η θ hηθ
      exact eq_of_heq ((h.left_map₂ η).symm.trans
        ((heq_of_eq (congrArg (fun η ↦ G.map₂ η) hηθ)).trans (h.left_map₂ θ)))
    · intro f g η
      obtain ⟨θ, hθ⟩ := transportMap₂ (h.left_obj X) (h.left_obj Y)
        (h.left_map f) (h.left_map g) (G.map₂ η)
      refine ⟨θ, eq_of_heq ?_⟩
      exact (map₂HEq F (h.left_obj X) (h.left_obj Y)
        (h.left_map f) (h.left_map g) hθ).symm.trans (h.right_map₂ η)
    · intro f
      obtain ⟨g, hg⟩ := transportMap (h.left_obj X) (h.left_obj Y) (G.map f)
      refine ⟨g, ⟨eqToIso (eq_of_heq ?_)⟩⟩
      exact (mapHEq F (h.left_obj X) (h.left_obj Y) hg).symm.trans (h.right_map f)
  · intro X
    exact ⟨G.obj X, ⟨Bicategory.eqToEquivalence (h.right_obj X)⟩⟩

/-- The chosen strict inverse in an equality-level inverse certificate is itself a
biequivalence after forgetting strictness. -/
theorem IsStrictInverse.rightIsBiequivalence
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    {F : StrictPseudofunctor B D} {G : StrictPseudofunctor D B}
    (h : IsStrictInverse F G) :
    Pseudofunctor.IsBiequivalence G.toPseudofunctor := by
  exact h.symm.leftIsBiequivalence

namespace IsStrictInverse

variable
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    {F : StrictPseudofunctor B D} {G : StrictPseudofunctor D B}

/-- The object component of the comparison from `F` followed by `G` to the identity. -/
def leftApp (h : IsStrictInverse F G) (X : B) :
    (F.toPseudofunctor.comp G.toPseudofunctor).obj X ⟶
      (Pseudofunctor.id B).obj X :=
  eqToHom (h.left_obj X)

/-- Transport a heterogeneous equality of `1`-morphisms across endpoint equalities.

The resulting comparison is an isomorphism because composition with identity `1`-morphisms
is only unital up to the bicategory's unitors. -/
private def naturalityIsoOfHEq
    {C : Type u₁} [Bicategory.{w₁, v₁} C]
    {a a' b b' : C} (p : a' = a) (q : b' = b)
    (f : a' ⟶ b') (g : a ⟶ b) (hfg : f ≍ g) :
    f ≫ eqToHom q ≅ eqToHom p ≫ g := by
  subst a
  subst b
  cases hfg
  exact (ρ_ f) ≪≫ (λ_ f).symm

/-- The endpoint-transport comparison is an equality when the bicategory is strict. -/
private theorem naturalityEqOfHEq
    {C : Type u₁} [Bicategory.{w₁, v₁} C] [Bicategory.Strict C]
    {a a' b b' : C} (p : a' = a) (q : b' = b)
    (f : a' ⟶ b') (g : a ⟶ b) (hfg : f ≍ g) :
    f ≫ eqToHom q = eqToHom p ≫ g := by
  subst a
  subst b
  cases hfg
  simp

/-- Naturality equality for the left strict-inverse comparison in a strict bicategory.

For a general bicategory the corresponding statement is only an isomorphism; use
`leftNaturalityIso` for that general statement. -/
theorem leftNaturality
    [Bicategory.Strict B] (h : IsStrictInverse F G) {X Y : B} (f : X ⟶ Y) :
    (F.toPseudofunctor.comp G.toPseudofunctor).map f ≫ leftApp h Y =
      leftApp h X ≫ (Pseudofunctor.id B).map f := by
  change G.map (F.map f) ≫ eqToHom (h.left_obj Y) =
    eqToHom (h.left_obj X) ≫ f
  exact naturalityEqOfHEq (h.left_obj X) (h.left_obj Y)
    (G.map (F.map f)) f (h.left_map f)

/-- Naturality isomorphism for the left strict-inverse comparison. -/
def leftNaturalityIso
    (h : IsStrictInverse F G) {X Y : B} (f : X ⟶ Y) :
    (F.toPseudofunctor.comp G.toPseudofunctor).map f ≫ leftApp h Y ≅
      leftApp h X ≫ (Pseudofunctor.id B).map f :=
  by
    change G.map (F.map f) ≫ eqToHom (h.left_obj Y) ≅
      eqToHom (h.left_obj X) ≫ f
    exact naturalityIsoOfHEq (h.left_obj X) (h.left_obj Y)
      (G.map (F.map f)) f (h.left_map f)

/-- Endpoint transport is compatible with the naturality of the unitors. -/
private theorem naturalityIsoOfHEq_map₂
    {a a' b b' : B} (p : a' = a) (q : b' = b)
    {f' g' : a' ⟶ b'} {f g : a ⟶ b} (hf : f' ≍ f) (hg : g' ≍ g)
    (η' : f' ⟶ g') (η : f ⟶ g) (hη : η' ≍ η) :
    η' ▷ eqToHom q ≫ (naturalityIsoOfHEq p q g' g hg).hom =
      (naturalityIsoOfHEq p q f' f hf).hom ≫ eqToHom p ◁ η := by
  subst a
  subst b
  cases hf
  cases hg
  cases hη
  simp [naturalityIsoOfHEq, Category.assoc]

/-- Endpoint transport satisfies identity coherence for a strict identity comparison. -/
private theorem naturalityIsoOfHEq_id
    {a a' : B} (p : a' = a) (f : a' ⟶ a') (hf : f ≍ 𝟙 a) (r : f = 𝟙 a') :
    (naturalityIsoOfHEq p p f (𝟙 a) hf).hom ≫ eqToHom p ◁ 𝟙 (𝟙 a) =
      eqToHom r ▷ eqToHom p ≫ (λ_ (eqToHom p)).hom ≫ (ρ_ (eqToHom p)).inv := by
  subst a
  subst f
  dsimp [naturalityIsoOfHEq]
  simp only [Iso.trans_hom, Iso.symm_hom]
  bicategory

/-- Endpoint transport satisfies composition coherence for a strict composition comparison. -/
private theorem naturalityIsoOfHEq_comp
    {a a' b b' c c' : B} (p : a' = a) (q : b' = b) (r : c' = c)
    (f' : a' ⟶ b') (g' : b' ⟶ c') (f : a ⟶ b) (g : b ⟶ c)
    (hf : f' ≍ f) (hg : g' ≍ g)
    (k : a' ⟶ c') (hk : k ≍ f ≫ g) (s : k = f' ≫ g') :
    (naturalityIsoOfHEq p r k (f ≫ g) hk).hom ≫ eqToHom p ◁ 𝟙 (f ≫ g) =
      eqToHom s ▷ eqToHom r ≫ (α_ _ _ _).hom ≫
        f' ◁ (naturalityIsoOfHEq q r g' g hg).hom ≫ (α_ _ _ _).inv ≫
        (naturalityIsoOfHEq p q f' f hf).hom ▷ g ≫ (α_ _ _ _).hom := by
  subst a
  subst b
  subst c
  cases hf
  cases hg
  subst k
  dsimp [naturalityIsoOfHEq]
  simp only [Iso.trans_hom, Iso.symm_hom]
  bicategory

/-- Modification naturality for the left strict-inverse comparison. -/
private theorem leftNaturalityNaturality
    (h : IsStrictInverse F G) {X Y : B} {f g : X ⟶ Y} (eta : f ⟶ g) :
    (F.toPseudofunctor.comp G.toPseudofunctor).map₂ eta ▷ leftApp h Y ≫
        (leftNaturalityIso h g).hom =
      (leftNaturalityIso h f).hom ≫
        leftApp h X ◁ (Pseudofunctor.id B).map₂ eta := by
  exact naturalityIsoOfHEq_map₂ (h.left_obj X) (h.left_obj Y)
    (h.left_map f) (h.left_map g) (G.map₂ (F.map₂ eta)) eta (h.left_map₂ eta)

/-- Identity coherence for the left strict-inverse comparison. -/
private theorem leftNaturalityId
    (h : IsStrictInverse F G) (X : B) :
    (leftNaturalityIso h (𝟙 X)).hom ≫
        leftApp h X ◁ ((Pseudofunctor.id B).mapId X).hom =
      ((F.toPseudofunctor.comp G.toPseudofunctor).mapId X).hom ▷ leftApp h X ≫
        (λ_ (leftApp h X)).hom ≫ (ρ_ (leftApp h X)).inv := by
  change (naturalityIsoOfHEq (h.left_obj X) (h.left_obj X)
    (G.map (F.map (𝟙 X))) (𝟙 X) (h.left_map (𝟙 X))).hom ≫
      eqToHom (h.left_obj X) ◁ 𝟙 (𝟙 X) =
    ((F.comp G).mapId X).hom ▷ eqToHom (h.left_obj X) ≫
      (λ_ (eqToHom (h.left_obj X))).hom ≫ (ρ_ (eqToHom (h.left_obj X))).inv
  rw [(F.comp G).mapId_eq_eqToIso]
  exact naturalityIsoOfHEq_id (h.left_obj X) _ (h.left_map (𝟙 X))
    ((F.comp G).map_id X)

/-- Composition coherence for the left strict-inverse comparison. -/
private theorem leftNaturalityComp
    (h : IsStrictInverse F G) {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (leftNaturalityIso h (f ≫ g)).hom ≫
        leftApp h X ◁ ((Pseudofunctor.id B).mapComp f g).hom =
      ((F.toPseudofunctor.comp G.toPseudofunctor).mapComp f g).hom ▷ leftApp h Z ≫
        (α_ _ _ _).hom ≫
        (F.toPseudofunctor.comp G.toPseudofunctor).map f ◁
          (leftNaturalityIso h g).hom ≫
        (α_ _ _ _).inv ≫
        (leftNaturalityIso h f).hom ▷ (Pseudofunctor.id B).map g ≫
        (α_ _ _ _).hom := by
  change (naturalityIsoOfHEq (h.left_obj X) (h.left_obj Z)
    (G.map (F.map (f ≫ g))) (f ≫ g) (h.left_map (f ≫ g))).hom ≫
      eqToHom (h.left_obj X) ◁ 𝟙 (f ≫ g) =
    ((F.comp G).mapComp f g).hom ▷ eqToHom (h.left_obj Z) ≫
      (α_ _ _ _).hom ≫
      G.map (F.map f) ◁ (leftNaturalityIso h g).hom ≫ (α_ _ _ _).inv ≫
      (leftNaturalityIso h f).hom ▷ g ≫ (α_ _ _ _).hom
  rw [(F.comp G).mapComp_eq_eqToIso]
  exact naturalityIsoOfHEq_comp (h.left_obj X) (h.left_obj Y) (h.left_obj Z)
    _ _ f g (h.left_map f) (h.left_map g) _ (h.left_map (f ≫ g))
    ((F.comp G).map_comp f g)

/-- The strong transformation from `F` followed by `G` to the identity determined by a strict
inverse certificate. -/
def leftTransformation (h : IsStrictInverse F G) :
    Pseudofunctor.StrongTrans
      (F.toPseudofunctor.comp G.toPseudofunctor) (Pseudofunctor.id B) where
  app := leftApp h
  naturality := leftNaturalityIso h
  naturality_naturality := leftNaturalityNaturality h
  naturality_id := leftNaturalityId h
  naturality_comp := leftNaturalityComp h

/-- The naturality isomorphism of the left strict-inverse transformation is the canonical
isomorphism obtained by endpoint transport and the bicategory unitors. -/
@[simp]
theorem leftTransformation.naturality
    (h : IsStrictInverse F G) {X Y : B} (f : X ⟶ Y) :
    (leftTransformation h).naturality f = leftNaturalityIso h f := by
  rfl

/-- The component of the left strict-inverse transformation is the equality-induced
`1`-morphism from the strict object comparison. -/
@[simp]
theorem leftTransformation.app (h : IsStrictInverse F G) (X : B) :
    (leftTransformation h).app X = eqToHom (h.left_obj X) := by
  rfl

/-- Pointwise adjoint-equivalence data on the left strict-inverse transformation. -/
def leftPointwiseEquivalence (h : IsStrictInverse F G) :
    Pseudofunctor.StrongTrans.PointwiseEquivalence (leftTransformation h) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (fun X ↦ Bicategory.eqToEquivalence (h.left_obj X))
    (fun X ↦ eqToIso ((Bicategory.eqToEquivalence.hom (h.left_obj X)).trans
      (leftTransformation.app h X).symm))

/-- The inverse component chosen by the left pointwise equivalence is the equality-induced
inverse of the strict object comparison. -/
@[simp]
theorem leftPointwiseEquivalence.invApp (h : IsStrictInverse F G) (X : B) :
    (leftPointwiseEquivalence h).invApp X = eqToHom (h.left_obj X).symm := by
  change (Bicategory.eqToEquivalence (h.left_obj X)).inv = _
  have inv_eq : ∀ {a b : B} (p : a = b),
      (Bicategory.eqToEquivalence p).inv = eqToHom p.symm := by
    intro a b p
    cases p
    rfl
  exact inv_eq _

/-- The equivalence from `F` followed by `G` to the identity determined by a strict inverse
certificate. -/
def leftEquivalence (h : IsStrictInverse F G) :
    F.toPseudofunctor.comp G.toPseudofunctor ≌ Pseudofunctor.id B :=
  (leftPointwiseEquivalence h).toEquivalence

/-- The forward transformation of the left equivalence is the canonical strict-inverse
comparison. -/
@[simp]
theorem leftEquivalence.hom (h : IsStrictInverse F G) :
    (leftEquivalence h).hom = leftTransformation h := by
  rfl

/-- The forward component of the left equivalence is induced by strict object equality. -/
@[simp]
theorem leftEquivalence.hom.app (h : IsStrictInverse F G) (X : B) :
    (leftEquivalence h).hom.app X = eqToHom (h.left_obj X) := by
  rfl

/-- The inverse component of the left equivalence is induced by reversed strict object
equality. -/
@[simp]
theorem leftEquivalence.inv.app (h : IsStrictInverse F G) (X : B) :
    (leftEquivalence h).inv.app X = eqToHom (h.left_obj X).symm := by
  exact leftPointwiseEquivalence.invApp h X

/-- The object component of the comparison from `G` followed by `F` to the identity. -/
def rightApp (h : IsStrictInverse F G) (X : D) :
    (G.toPseudofunctor.comp F.toPseudofunctor).obj X ⟶
      (Pseudofunctor.id D).obj X :=
  eqToHom (h.right_obj X)

/-- Naturality equality for the right strict-inverse comparison in a strict bicategory.

For a general bicategory the corresponding statement is only an isomorphism; use
`rightNaturalityIso` for that general statement. -/
theorem rightNaturality
    [Bicategory.Strict D] (h : IsStrictInverse F G) {X Y : D} (f : X ⟶ Y) :
    (G.toPseudofunctor.comp F.toPseudofunctor).map f ≫ rightApp h Y =
      rightApp h X ≫ (Pseudofunctor.id D).map f := by
  change F.map (G.map f) ≫ eqToHom (h.right_obj Y) =
    eqToHom (h.right_obj X) ≫ f
  exact naturalityEqOfHEq (h.right_obj X) (h.right_obj Y)
    (F.map (G.map f)) f (h.right_map f)

/-- Naturality isomorphism for the right strict-inverse comparison. -/
def rightNaturalityIso
    (h : IsStrictInverse F G) {X Y : D} (f : X ⟶ Y) :
    (G.toPseudofunctor.comp F.toPseudofunctor).map f ≫ rightApp h Y ≅
      rightApp h X ≫ (Pseudofunctor.id D).map f :=
  by
    change F.map (G.map f) ≫ eqToHom (h.right_obj Y) ≅
      eqToHom (h.right_obj X) ≫ f
    exact naturalityIsoOfHEq (h.right_obj X) (h.right_obj Y)
      (F.map (G.map f)) f (h.right_map f)

/-- Modification naturality for the right strict-inverse comparison. -/
private theorem rightNaturalityNaturality
    (h : IsStrictInverse F G) {X Y : D} {f g : X ⟶ Y} (eta : f ⟶ g) :
    (G.toPseudofunctor.comp F.toPseudofunctor).map₂ eta ▷ rightApp h Y ≫
        (rightNaturalityIso h g).hom =
      (rightNaturalityIso h f).hom ≫
        rightApp h X ◁ (Pseudofunctor.id D).map₂ eta := by
  exact leftNaturalityNaturality h.symm eta

/-- Identity coherence for the right strict-inverse comparison. -/
private theorem rightNaturalityId
    (h : IsStrictInverse F G) (X : D) :
    (rightNaturalityIso h (𝟙 X)).hom ≫
        rightApp h X ◁ ((Pseudofunctor.id D).mapId X).hom =
      ((G.toPseudofunctor.comp F.toPseudofunctor).mapId X).hom ▷ rightApp h X ≫
        (λ_ (rightApp h X)).hom ≫ (ρ_ (rightApp h X)).inv := by
  exact leftNaturalityId h.symm X

/-- Composition coherence for the right strict-inverse comparison. -/
private theorem rightNaturalityComp
    (h : IsStrictInverse F G) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (rightNaturalityIso h (f ≫ g)).hom ≫
        rightApp h X ◁ ((Pseudofunctor.id D).mapComp f g).hom =
      ((G.toPseudofunctor.comp F.toPseudofunctor).mapComp f g).hom ▷ rightApp h Z ≫
        (α_ _ _ _).hom ≫
        (G.toPseudofunctor.comp F.toPseudofunctor).map f ◁
          (rightNaturalityIso h g).hom ≫
        (α_ _ _ _).inv ≫
        (rightNaturalityIso h f).hom ▷ (Pseudofunctor.id D).map g ≫
        (α_ _ _ _).hom := by
  exact leftNaturalityComp h.symm f g

/-- The strong transformation from `G` followed by `F` to the identity determined by a strict
inverse certificate. -/
def rightTransformation (h : IsStrictInverse F G) :
    Pseudofunctor.StrongTrans
      (G.toPseudofunctor.comp F.toPseudofunctor) (Pseudofunctor.id D) where
  app := rightApp h
  naturality := rightNaturalityIso h
  naturality_naturality := rightNaturalityNaturality h
  naturality_id := rightNaturalityId h
  naturality_comp := rightNaturalityComp h

/-- The naturality isomorphism of the right strict-inverse transformation is the canonical
isomorphism obtained by endpoint transport and the bicategory unitors. -/
@[simp]
theorem rightTransformation.naturality
    (h : IsStrictInverse F G) {X Y : D} (f : X ⟶ Y) :
    (rightTransformation h).naturality f = rightNaturalityIso h f := by
  rfl

/-- The component of the right strict-inverse transformation is the equality-induced
`1`-morphism from the strict object comparison. -/
@[simp]
theorem rightTransformation.app (h : IsStrictInverse F G) (X : D) :
    (rightTransformation h).app X = eqToHom (h.right_obj X) := by
  rfl

/-- Pointwise adjoint-equivalence data on the right strict-inverse transformation. -/
def rightPointwiseEquivalence (h : IsStrictInverse F G) :
    Pseudofunctor.StrongTrans.PointwiseEquivalence (rightTransformation h) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (fun X ↦ Bicategory.eqToEquivalence (h.right_obj X))
    (fun X ↦ eqToIso ((Bicategory.eqToEquivalence.hom (h.right_obj X)).trans
      (rightTransformation.app h X).symm))

/-- The inverse component chosen by the right pointwise equivalence is the equality-induced
inverse of the strict object comparison. -/
@[simp]
theorem rightPointwiseEquivalence.invApp (h : IsStrictInverse F G) (X : D) :
    (rightPointwiseEquivalence h).invApp X = eqToHom (h.right_obj X).symm := by
  change (Bicategory.eqToEquivalence (h.right_obj X)).inv = _
  have inv_eq : ∀ {a b : D} (p : a = b),
      (Bicategory.eqToEquivalence p).inv = eqToHom p.symm := by
    intro a b p
    cases p
    rfl
  exact inv_eq _

/-- The equivalence from `G` followed by `F` to the identity determined by a strict inverse
certificate. -/
def rightEquivalence (h : IsStrictInverse F G) :
    G.toPseudofunctor.comp F.toPseudofunctor ≌ Pseudofunctor.id D :=
  (rightPointwiseEquivalence h).toEquivalence

/-- The forward transformation of the right equivalence is the canonical strict-inverse
comparison. -/
@[simp]
theorem rightEquivalence.hom (h : IsStrictInverse F G) :
    (rightEquivalence h).hom = rightTransformation h := by
  rfl

/-- The forward component of the right equivalence is induced by strict object equality. -/
@[simp]
theorem rightEquivalence.hom.app (h : IsStrictInverse F G) (X : D) :
    (rightEquivalence h).hom.app X = eqToHom (h.right_obj X) := by
  rfl

/-- The inverse component of the right equivalence is induced by reversed strict object
equality. -/
@[simp]
theorem rightEquivalence.inv.app (h : IsStrictInverse F G) (X : D) :
    (rightEquivalence h).inv.app X = eqToHom (h.right_obj X).symm := by
  exact rightPointwiseEquivalence.invApp h X

/-- Promote an equality-level strict inverse certificate to explicit weak-inverse data. -/
def toWeakInverse (h : IsStrictInverse F G) :
    Pseudofunctor.WeakInverse F.toPseudofunctor G.toPseudofunctor where
  left := leftEquivalence h
  right := rightEquivalence h

/-- The left equivalence stored by `toWeakInverse` is the canonical left strict-inverse
equivalence. -/
@[simp]
theorem toWeakInverse.left (h : IsStrictInverse F G) :
    (toWeakInverse h).left = leftEquivalence h := by
  rfl

/-- The right equivalence stored by `toWeakInverse` is the canonical right strict-inverse
equivalence. -/
@[simp]
theorem toWeakInverse.right (h : IsStrictInverse F G) :
    (toWeakInverse h).right = rightEquivalence h := by
  rfl

/-- The forward component of the left equivalence stored by `toWeakInverse` is induced by the
left strict object equality. -/
@[simp]
theorem toWeakInverse.left.hom.app (h : IsStrictInverse F G) (X : B) :
    (toWeakInverse h).left.hom.app X = eqToHom (h.left_obj X) := by
  rfl

/-- The inverse component of the left equivalence stored by `toWeakInverse` is induced by the
reversed left strict object equality. -/
@[simp]
theorem toWeakInverse.left.inv.app (h : IsStrictInverse F G) (X : B) :
    (toWeakInverse h).left.inv.app X = eqToHom (h.left_obj X).symm := by
  exact leftPointwiseEquivalence.invApp h X

/-- The forward component of the right equivalence stored by `toWeakInverse` is induced by the
right strict object equality. -/
@[simp]
theorem toWeakInverse.right.hom.app (h : IsStrictInverse F G) (X : D) :
    (toWeakInverse h).right.hom.app X = eqToHom (h.right_obj X) := by
  rfl

/-- The inverse component of the right equivalence stored by `toWeakInverse` is induced by the
reversed right strict object equality. -/
@[simp]
theorem toWeakInverse.right.inv.app (h : IsStrictInverse F G) (X : D) :
    (toWeakInverse h).right.inv.app X = eqToHom (h.right_obj X).symm := by
  exact rightPointwiseEquivalence.invApp h X

end IsStrictInverse

end CategoryTheory.StrictPseudofunctor
