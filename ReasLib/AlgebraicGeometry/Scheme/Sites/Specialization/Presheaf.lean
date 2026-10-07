module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Data.ZMod.Basic

/-!
# Presheaves on specialization chains

Concrete `ZMod 2`-valued presheaves indexed by strict specialization pairs and
finite strict specialization chains of schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped Classical

universe u

namespace AlgebraicGeometry.Scheme.Specialization

/-- A chain `x 0, …, x n` is strict when each consecutive pair is a distinct specialization. -/
def IsStrictChain {n : ℕ} {X : Scheme.{u}} (x : Fin (n + 1) → X) : Prop :=
  ∀ i : Fin n, x i.succ ⤳ x i.castSucc ∧ x i.succ ≠ x i.castSucc

/-- The index type of distinct specialization pairs in a scheme. -/
abbrev pairIndex (X : Scheme.{u}) : Type u :=
  { p : X × X // p.2 ⤳ p.1 ∧ p.2 ≠ p.1 }

/-- The index type of strict specialization chains of length `n` in a scheme. -/
abbrev chainIndex (n : ℕ) (X : Scheme.{u}) : Type u :=
  { x : Fin (n + 1) → X // IsStrictChain x }

/-- The `ZMod 2`-valued sections indexed by distinct specialization pairs. -/
abbrev pairSections (X : Scheme.{u}) : Type u := pairIndex X → ZMod 2

/-- The `ZMod 2`-valued sections indexed by strict specialization chains of length `n`. -/
abbrev chainSections (n : ℕ) (X : Scheme.{u}) : Type u := chainIndex n X → ZMod 2

/-- Restriction of pair-indexed sections along a scheme morphism. -/
noncomputable def pairRestrict {X Y : Scheme.{u}} (f : Y ⟶ X) :
    pairSections X →+ pairSections Y :=
  AddMonoidHom.mk'
    (fun a p ↦
      if h : f p.1.2 ≠ f p.1.1 then
        a ⟨(f p.1.1, f p.1.2), ⟨f.base.hom.map_specializes p.2.1, h⟩⟩
      else 0)
    (fun _ _ ↦ sorry)

/-- Restriction of chain-indexed sections along a scheme morphism. -/
noncomputable def chainRestrict (n : ℕ) {X Y : Scheme.{u}} (f : Y ⟶ X) :
    chainSections n X →+ chainSections n Y :=
  AddMonoidHom.mk'
    (fun a x ↦
      if h : IsStrictChain (f ∘ x.1) then a ⟨f ∘ x.1, h⟩ else 0)
    (fun _ _ ↦ sorry)

/-- The pointwise formula for restriction of pair-indexed sections. -/
theorem pairRestrict_apply {X Y : Scheme.{u}} (f : Y ⟶ X) (a : pairSections X)
    (p : pairIndex Y) :
    pairRestrict f a p =
      if h : f p.1.2 ≠ f p.1.1 then
        a ⟨(f p.1.1, f p.1.2), ⟨f.base.hom.map_specializes p.2.1, h⟩⟩
      else 0 := sorry

/-- The pointwise formula for restriction of chain-indexed sections. -/
theorem chainRestrict_apply (n : ℕ) {X Y : Scheme.{u}} (f : Y ⟶ X)
    (a : chainSections n X) (x : chainIndex n Y) :
    chainRestrict n f a x =
      if h : IsStrictChain (f ∘ x.1) then a ⟨f ∘ x.1, h⟩ else 0 := sorry

/-- Identity restriction for pair-indexed sections, expressed in the additive-group category. -/
theorem pairRestrict_id (X : Scheme.{u}ᵒᵖ) :
    AddCommGrpCat.ofHom (pairRestrict (𝟙 X.unop)) =
      𝟙 (AddCommGrpCat.of (pairSections X.unop)) := sorry

/-- Composite restriction for pair-indexed sections, contravariantly in schemes. -/
theorem pairRestrict_comp {X Y Z : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    AddCommGrpCat.ofHom (pairRestrict (g.unop ≫ f.unop)) =
      AddCommGrpCat.ofHom (pairRestrict f.unop) ≫
        AddCommGrpCat.ofHom (pairRestrict g.unop) := sorry

/-- Identity restriction for chain-indexed sections, expressed in the additive-group category. -/
theorem chainRestrict_id (n : ℕ) (X : Scheme.{u}ᵒᵖ) :
    AddCommGrpCat.ofHom (chainRestrict n (𝟙 X.unop)) =
      𝟙 (AddCommGrpCat.of (chainSections n X.unop)) := sorry

/-- Composite restriction for chain-indexed sections, contravariantly in schemes. -/
theorem chainRestrict_comp (n : ℕ) {X Y Z : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    AddCommGrpCat.ofHom (chainRestrict n (g.unop ≫ f.unop)) =
      AddCommGrpCat.ofHom (chainRestrict n f.unop) ≫
        AddCommGrpCat.ofHom (chainRestrict n g.unop) := sorry

/-- The specialization-pair presheaf on the big étale site. -/
noncomputable def pairPresheaf : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (pairSections X.unop)
  map f := AddCommGrpCat.ofHom (pairRestrict f.unop)
  map_id X := pairRestrict_id X
  map_comp f g := pairRestrict_comp f g

/-- The specialization-chain presheaf of length `n` on the big étale site. -/
noncomputable def chainPresheaf (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj X := AddCommGrpCat.of (chainSections n X.unop)
  map f := AddCommGrpCat.ofHom (chainRestrict n f.unop)
  map_id X := chainRestrict_id n X
  map_comp f g := chainRestrict_comp n f g

/-- Objectwise, the pair presheaf has the pair-section group. -/
theorem pairPresheaf_obj (X : Scheme.{u}ᵒᵖ) :
    pairPresheaf.obj X = AddCommGrpCat.of (pairSections X.unop) := sorry

/-- Objectwise, the length-`n` chain presheaf has the chain-section group. -/
theorem chainPresheaf_obj (n : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (chainPresheaf n).obj X = AddCommGrpCat.of (chainSections n X.unop) := sorry

/-- The morphism of the pair presheaf is the corresponding pair restriction. -/
theorem pairPresheaf_map {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    pairPresheaf.map f = AddCommGrpCat.ofHom (pairRestrict f.unop) := sorry

/-- The morphism of the chain presheaf is the corresponding chain restriction. -/
theorem chainPresheaf_map (n : ℕ) {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (chainPresheaf n).map f = AddCommGrpCat.ofHom (chainRestrict n f.unop) := sorry

end AlgebraicGeometry.Scheme.Specialization
