/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.LeftKanExtension.Map
public import ReasLib.CategoryTheory.Functor.RightKanExtension.Map
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0183

# Pointwise Kan extensions of truncated simplicial objects

This leaf owns the full-inclusion coskeleton and skeleton predicates, their chosen objects, and
the universal map APIs. It is independent of finite (co)limit existence instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Truncated

/-- A truncated simplicial object admits its `n`-coskeleton. -/
@[stacks 0183 "existence of an objectwise coskeleton"]
abbrev HasCoskeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) : Prop :=
  (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension U

/-- A truncated simplicial object admits its `n`-coskeleton as a pointwise right Kan
extension. -/
@[stacks 0183 "pointwise construction of an objectwise coskeleton"]
abbrev HasPointwiseCoskeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) : Prop :=
  (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension U

/-- A truncated simplicial object admits its `n`-skeleton. -/
@[stacks 018N "existence of an objectwise skeleton"]
abbrev HasSkeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) : Prop :=
  (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension U

/-- A truncated simplicial object admits its `n`-skeleton as a pointwise left Kan extension. -/
@[stacks 018N "pointwise construction of an objectwise skeleton"]
abbrev HasPointwiseSkeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) : Prop :=
  (SimplexCategory.Truncated.inclusion n).op.HasPointwiseLeftKanExtension U

/-- The chosen objectwise coskeleton of a truncated simplicial object. -/
@[stacks 0181 "chosen objectwise coskeleton"]
protected noncomputable abbrev coskeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasCoskeleton] : SimplicialObject C :=
  (SimplexCategory.Truncated.inclusion n).op.rightKanExtension U

/-- The chosen objectwise skeleton of a truncated simplicial object. -/
@[stacks 018N "chosen objectwise skeleton"]
protected noncomputable abbrev skeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasSkeleton] : SimplicialObject C :=
  (SimplexCategory.Truncated.inclusion n).op.leftKanExtension U

namespace coskeleton

/-- The counit of the chosen objectwise coskeleton of `U`. -/
@[stacks 0181 "chosen objectwise coskeleton counit"]
noncomputable def counit {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasCoskeleton] :
    (SimplexCategory.Truncated.inclusion n).op ⋙ U.coskeleton ⟶ U :=
  (SimplexCategory.Truncated.inclusion n).op.rightKanExtensionCounit U

/-- The universal lift from a simplicial object to a chosen objectwise coskeleton. -/
@[stacks 0181 "lift to a chosen objectwise coskeleton"]
noncomputable def lift {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasCoskeleton]
    (V : SimplicialObject C)
    (f : (SimplexCategory.Truncated.inclusion n).op ⋙ V ⟶ U) :
    V ⟶ U.coskeleton :=
  Functor.RightKanExtension.lift
    (SimplexCategory.Truncated.inclusion n).op U V f

/-- A coskeleton lift recovers the natural transformation from which it was constructed. -/
@[reassoc (attr := simp), stacks 0181 "coskeleton lift on the counit"]
theorem lift_counit {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasCoskeleton]
    (V : SimplicialObject C)
    (f : (SimplexCategory.Truncated.inclusion n).op ⋙ V ⟶ U) :
    (SimplexCategory.Truncated.inclusion n).op.whiskerLeft (lift U V f) ≫
        counit U =
      f := sorry

/-- The universal Hom-equivalence of a chosen objectwise coskeleton. -/
@[stacks 0181 "Hom equivalence for a chosen objectwise coskeleton"]
noncomputable def homEquiv {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasCoskeleton]
    (V : SimplicialObject C) :
    (V ⟶ U.coskeleton) ≃
      ((SimplexCategory.Truncated.inclusion n).op ⋙ V ⟶ U) :=
  Functor.RightKanExtension.homEquiv
    (SimplexCategory.Truncated.inclusion n).op U V

/-- The forward coskeleton Hom-equivalence is restriction followed by the counit. -/
@[simp, stacks 0181 "forward coskeleton Hom equivalence"]
theorem homEquiv_apply {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasCoskeleton]
    (V : SimplicialObject C) (f : V ⟶ U.coskeleton) :
    homEquiv U V f =
      (SimplexCategory.Truncated.inclusion n).op.whiskerLeft f ≫ counit U := sorry

/-- The inverse coskeleton Hom-equivalence is the universal lift. -/
@[simp, stacks 0181 "inverse coskeleton Hom equivalence"]
theorem homEquiv_symm_apply {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasCoskeleton]
    (V : SimplicialObject C)
    (f : (SimplexCategory.Truncated.inclusion n).op ⋙ V ⟶ U) :
    (homEquiv U V).symm f = lift U V f := sorry

/-- The morphism of chosen objectwise coskeletons induced by a truncated simplicial morphism. -/
@[stacks 018C "map between chosen objectwise coskeletons"]
noncomputable abbrev map {C : Type u} [Category.{v} C] {n : ℕ}
    {U V : SimplicialObject.Truncated C n} [U.HasCoskeleton] [V.HasCoskeleton]
    (f : U ⟶ V) : U.coskeleton ⟶ V.coskeleton :=
  Functor.RightKanExtension.map
    (SimplexCategory.Truncated.inclusion n).op f

/-- A chosen objectwise coskeleton map commutes with the coskeleton counits. -/
@[reassoc (attr := simp), stacks 018C "objectwise coskeleton map and counit"]
theorem map_counit {C : Type u} [Category.{v} C] {n : ℕ}
    {U V : SimplicialObject.Truncated C n} [U.HasCoskeleton] [V.HasCoskeleton]
    (f : U ⟶ V) :
    (SimplexCategory.Truncated.inclusion n).op.whiskerLeft (map f) ≫ counit V =
      counit U ≫ f := sorry

/-- The chosen objectwise coskeleton map associated to an identity is the identity. -/
@[simp, stacks 018C "identity map between chosen objectwise coskeletons"]
theorem map_id {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasCoskeleton] :
    map (𝟙 U) = 𝟙 U.coskeleton := sorry

/-- Chosen objectwise coskeleton maps respect composition. -/
@[stacks 018C "composition of chosen objectwise coskeleton maps"]
theorem map_comp {C : Type u} [Category.{v} C] {n : ℕ}
    {U V W : SimplicialObject.Truncated C n}
    [U.HasCoskeleton] [V.HasCoskeleton] [W.HasCoskeleton]
    (f : U ⟶ V) (g : V ⟶ W) :
    map (f ≫ g) = map f ≫ map g := sorry

end coskeleton

namespace skeleton

/-- The unit of the chosen objectwise skeleton of `U`. -/
@[stacks 018N "chosen objectwise skeleton unit"]
noncomputable def unit {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasSkeleton] :
    U ⟶ (SimplexCategory.Truncated.inclusion n).op ⋙ U.skeleton :=
  (SimplexCategory.Truncated.inclusion n).op.leftKanExtensionUnit U

/-- The universal descent map from a chosen objectwise skeleton. -/
@[stacks 018N "descent from a chosen objectwise skeleton"]
noncomputable def desc {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasSkeleton]
    (V : SimplicialObject C)
    (f : U ⟶ (SimplexCategory.Truncated.inclusion n).op ⋙ V) :
    U.skeleton ⟶ V :=
  Functor.LeftKanExtension.desc
    (SimplexCategory.Truncated.inclusion n).op U V f

/-- The skeleton unit followed by a descent map recovers its defining transformation. -/
@[reassoc (attr := simp), stacks 018N "skeleton unit followed by descent"]
theorem unit_desc {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasSkeleton]
    (V : SimplicialObject C)
    (f : U ⟶ (SimplexCategory.Truncated.inclusion n).op ⋙ V) :
    unit U ≫
        (SimplexCategory.Truncated.inclusion n).op.whiskerLeft (desc U V f) =
      f := sorry

/-- The universal Hom-equivalence of a chosen objectwise skeleton. -/
@[stacks 018N "Hom equivalence for a chosen objectwise skeleton"]
noncomputable def homEquiv {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasSkeleton]
    (V : SimplicialObject C) :
    (U.skeleton ⟶ V) ≃
      (U ⟶ (SimplexCategory.Truncated.inclusion n).op ⋙ V) :=
  Functor.LeftKanExtension.homEquiv
    (SimplexCategory.Truncated.inclusion n).op U V

/-- The forward skeleton Hom-equivalence is the unit followed by restriction. -/
@[simp, stacks 018N "forward skeleton Hom equivalence"]
theorem homEquiv_apply {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasSkeleton]
    (V : SimplicialObject C) (f : U.skeleton ⟶ V) :
    homEquiv U V f =
      unit U ≫ (SimplexCategory.Truncated.inclusion n).op.whiskerLeft f := sorry

/-- The inverse skeleton Hom-equivalence is the universal descent map. -/
@[simp, stacks 018N "inverse skeleton Hom equivalence"]
theorem homEquiv_symm_apply {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasSkeleton]
    (V : SimplicialObject C)
    (f : U ⟶ (SimplexCategory.Truncated.inclusion n).op ⋙ V) :
    (homEquiv U V).symm f = desc U V f := sorry

/-- The morphism of chosen objectwise skeletons induced by a truncated simplicial morphism. -/
@[stacks 018N "map between chosen objectwise skeletons"]
noncomputable abbrev map {C : Type u} [Category.{v} C] {n : ℕ}
    {U V : SimplicialObject.Truncated C n} [U.HasSkeleton] [V.HasSkeleton]
    (f : U ⟶ V) : U.skeleton ⟶ V.skeleton :=
  Functor.LeftKanExtension.map
    (SimplexCategory.Truncated.inclusion n).op f

/-- A chosen objectwise skeleton map commutes with the skeleton units. -/
@[reassoc (attr := simp), stacks 018N "objectwise skeleton unit and map"]
theorem unit_map {C : Type u} [Category.{v} C] {n : ℕ}
    {U V : SimplicialObject.Truncated C n} [U.HasSkeleton] [V.HasSkeleton]
    (f : U ⟶ V) :
    unit U ≫ (SimplexCategory.Truncated.inclusion n).op.whiskerLeft (map f) =
      f ≫ unit V := sorry

/-- The chosen objectwise skeleton map associated to an identity is the identity. -/
@[simp, stacks 018N "identity map between chosen objectwise skeletons"]
theorem map_id {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) [U.HasSkeleton] :
    map (𝟙 U) = 𝟙 U.skeleton := sorry

/-- Chosen objectwise skeleton maps respect composition. -/
@[stacks 018N "composition of chosen objectwise skeleton maps"]
theorem map_comp {C : Type u} [Category.{v} C] {n : ℕ}
    {U V W : SimplicialObject.Truncated C n}
    [U.HasSkeleton] [V.HasSkeleton] [W.HasSkeleton]
    (f : U ⟶ V) (g : V ⟶ W) :
    map (f ≫ g) = map f ≫ map g := sorry

end skeleton

/-- The coefficient category admits all `n`-coskeletons. -/
@[stacks 0183 "existence of coskeletons"]
abbrev HasCoskeletons (C : Type u) [Category.{v} C] (n : ℕ) : Prop :=
  ∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
    CategoryTheory.SimplicialObject.Truncated.HasCoskeleton F

/-- The coefficient category admits all `n`-coskeletons as pointwise right Kan extensions. -/
@[stacks 0183 "pointwise construction of coskeletons"]
abbrev HasPointwiseCoskeletons (C : Type u) [Category.{v} C] (n : ℕ) : Prop :=
  ∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
    CategoryTheory.SimplicialObject.Truncated.HasPointwiseCoskeleton F

/-- The coefficient category admits all `n`-skeletons. -/
@[stacks 018N "existence of skeletons"]
abbrev HasSkeletons (C : Type u) [Category.{v} C] (n : ℕ) : Prop :=
  ∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
    CategoryTheory.SimplicialObject.Truncated.HasSkeleton F

/-- The coefficient category admits all `n`-skeletons as pointwise left Kan extensions. -/
@[stacks 018N "pointwise construction of skeletons"]
abbrev HasPointwiseSkeletons (C : Type u) [Category.{v} C] (n : ℕ) : Prop :=
  ∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
    CategoryTheory.SimplicialObject.Truncated.HasPointwiseSkeleton F

end CategoryTheory.SimplicialObject.Truncated
