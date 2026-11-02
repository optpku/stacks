/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.DividedPowers.Scheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Pullbacks

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

@[expose] public section

universe u

namespace DividedPowerScheme

/-- The identity scheme morphism preserves the divided-power ideal. -/
lemma Hom.id_ideal_compatible (X : DividedPowerScheme.{u}) :
    X.ideal.comap (𝟙 X.scheme : X.scheme ⟶ X.scheme) ≤ X.ideal := by
  simp only [Scheme.IdealSheafData.comap_id, le_refl]

/-- The identity scheme morphism preserves divided powers on affine sections. -/
lemma Hom.id_dividedPowers_compatible (X : DividedPowerScheme.{u}) :
    ∀ (V : X.scheme.affineOpens) (W : X.scheme.affineOpens)
      (hVW : W.1 ≤ (𝟙 X.scheme : X.scheme ⟶ X.scheme) ⁻¹ᵁ V.1),
      (X.dividedPowers V).IsDPMorphism (X.dividedPowers W)
        ((𝟙 X.scheme : X.scheme ⟶ X.scheme).appLE V.1 W.1 hVW).hom := sorry

/-- Composition preserves the divided-power ideal. -/
lemma Hom.comp_ideal_compatible {X Y Z : DividedPowerScheme.{u}}
    (f : Hom X Y) (g : Hom Y Z) :
    Z.ideal.comap (f.base ≫ g.base) ≤ X.ideal := by
  rw [Scheme.IdealSheafData.comap_comp]
  exact (Scheme.IdealSheafData.comap_mono f.base g.ideal_compatible).trans f.ideal_compatible

/-- Composition preserves divided powers on affine sections. -/
lemma Hom.comp_dividedPowers_compatible {X Y Z : DividedPowerScheme.{u}}
    (f : Hom X Y) (g : Hom Y Z) :
    ∀ (V : Z.scheme.affineOpens) (W : X.scheme.affineOpens)
      (hVW : W.1 ≤ (f.base ≫ g.base) ⁻¹ᵁ V.1),
      (Z.dividedPowers V).IsDPMorphism (X.dividedPowers W)
        ((f.base ≫ g.base).appLE V.1 W.1 hVW).hom := sorry

/-- The identity morphism of a divided-power scheme. -/
def Hom.id (X : DividedPowerScheme.{u}) : Hom X X where
  base := 𝟙 X.scheme
  ideal_compatible := Hom.id_ideal_compatible X
  dividedPowers_compatible := Hom.id_dividedPowers_compatible X

/-- Composition of morphisms of divided-power schemes. -/
def Hom.comp {X Y Z : DividedPowerScheme.{u}}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  ideal_compatible := Hom.comp_ideal_compatible f g
  dividedPowers_compatible := Hom.comp_dividedPowers_compatible f g

/-- The underlying scheme map of the identity divided-power morphism. -/
lemma Hom.id_base (X : DividedPowerScheme.{u}) :
    (Hom.id X).base = 𝟙 X.scheme := rfl

/-- The underlying scheme map of a composite divided-power morphism. -/
lemma Hom.comp_base {X Y Z : DividedPowerScheme.{u}}
    (f : Hom X Y) (g : Hom Y Z) :
    (Hom.comp f g).base = f.base ≫ g.base := rfl

/-- Divided-power scheme morphisms are determined by their underlying scheme maps. -/
@[ext]
lemma Hom.ext {X Y : DividedPowerScheme.{u}} {f g : Hom X Y}
    (h : f.base = g.base) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Left identity for composition of divided-power scheme morphisms. -/
lemma Hom.id_comp {X Y : DividedPowerScheme.{u}} (f : Hom X Y) :
    Hom.comp (Hom.id X) f = f := by
  apply Hom.ext
  exact Category.id_comp f.base

/-- Right identity for composition of divided-power scheme morphisms. -/
lemma Hom.comp_id {X Y : DividedPowerScheme.{u}} (f : Hom X Y) :
    Hom.comp f (Hom.id Y) = f := by
  apply Hom.ext
  exact Category.comp_id f.base

/-- Associativity of composition of divided-power scheme morphisms. -/
lemma Hom.assoc {W X Y Z : DividedPowerScheme.{u}}
    (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := by
  apply Hom.ext
  exact Category.assoc f.base g.base h.base

/-- The explicit category whose objects are divided-power schemes and whose arrows
are divided-power scheme morphisms. -/
@[reducible] def category : Category DividedPowerScheme where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- The morphism induced on the closed subschemes defined by the divided-power ideals. -/
noncomputable def Hom.zeroFiberMap {X Y : DividedPowerScheme.{u}} (f : Hom X Y) :
    X.ideal.subscheme ⟶ Y.ideal.subscheme :=
  Scheme.IdealSheafData.subschemeMap X.ideal Y.ideal f.base
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr f.ideal_compatible)

/-- The zero-fibre morphism commutes with the canonical closed-subscheme immersions. -/
lemma Hom.zeroFiberMap_comm {X Y : DividedPowerScheme.{u}} (f : Hom X Y) :
    f.zeroFiberMap ≫ Y.ideal.subschemeι = X.ideal.subschemeι ≫ f.base := by
  exact Scheme.IdealSheafData.subschemeMap_subschemeι X.ideal Y.ideal f.base
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr f.ideal_compatible)

/-- The zero-fibre map respects composition of divided-power scheme morphisms. -/
lemma Hom.zeroFiberMap_comp {X Y Z : DividedPowerScheme.{u}}
    (f : Hom X Y) (g : Hom Y Z) :
    (Hom.comp f g).zeroFiberMap = f.zeroFiberMap ≫ g.zeroFiberMap := by
  apply (cancel_mono Z.ideal.subschemeι).mp
  calc
    _ = X.ideal.subschemeι ≫ (f.base ≫ g.base) := (Hom.comp f g).zeroFiberMap_comm
    _ = (f.zeroFiberMap ≫ Y.ideal.subschemeι) ≫ g.base := by
      rw [f.zeroFiberMap_comm, Category.assoc]
    _ = f.zeroFiberMap ≫ (g.zeroFiberMap ≫ Z.ideal.subschemeι) := by
      rw [g.zeroFiberMap_comm, Category.assoc]
    _ = _ := (Category.assoc _ _ _).symm

/-- The canonical categorical pullback predicate for divided-power scheme morphisms. -/
abbrev IsPullback {P X Y Z : DividedPowerScheme.{u}}
    (fst : Hom P X) (snd : Hom P Y) (f : Hom X Z) (g : Hom Y Z) : Prop :=
  @CategoryTheory.IsPullback DividedPowerScheme category P X Y Z fst snd f g

namespace IsPullback

/-- The universal morphism into a divided-power pullback square. -/
noncomputable def lift
    {P X Y Z W : DividedPowerScheme.{u}}
    {fst : Hom P X} {snd : Hom P Y} {f : Hom X Z} {g : Hom Y Z}
    (hP : IsPullback fst snd f g) (a : Hom W X) (b : Hom W Y)
    (w : Hom.comp a f = Hom.comp b g) : Hom W P :=
  @CategoryTheory.IsPullback.lift DividedPowerScheme category P X Y Z fst snd f g
    hP W a b w

/-- The first projection law for the universal morphism into a divided-power pullback. -/
lemma lift_fst
    {P X Y Z W : DividedPowerScheme.{u}}
    {fst : Hom P X} {snd : Hom P Y} {f : Hom X Z} {g : Hom Y Z}
    (hP : IsPullback fst snd f g) (a : Hom W X) (b : Hom W Y)
    (w : Hom.comp a f = Hom.comp b g) :
    Hom.comp (lift hP a b w) fst = a := by
  exact @CategoryTheory.IsPullback.lift_fst DividedPowerScheme category P X Y Z fst snd f g
    hP W a b w

/-- The second projection law for the universal morphism into a divided-power pullback. -/
lemma lift_snd
    {P X Y Z W : DividedPowerScheme.{u}}
    {fst : Hom P X} {snd : Hom P Y} {f : Hom X Z} {g : Hom Y Z}
    (hP : IsPullback fst snd f g) (a : Hom W X) (b : Hom W Y)
    (w : Hom.comp a f = Hom.comp b g) :
    Hom.comp (lift hP a b w) snd = b := by
  exact @CategoryTheory.IsPullback.lift_snd DividedPowerScheme category P X Y Z fst snd f g
    hP W a b w

end IsPullback

end DividedPowerScheme
