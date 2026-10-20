/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Regular.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Descent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.LocalCriterion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity

/-!
# Descent of smooth morphisms

This file records descent of smoothness along surjective smooth morphisms of schemes and under
fppf precomposition, as well as pointwise flat descent and flat-surjective descent over fields.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Smooth

/-- Smoothness descends under precomposition by a surjective, flat, locally finitely
presented morphism. -/
instance hasOfPrecompFppf :
    MorphismProperty.HasOfPrecompProperty
      (@Smooth : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
        MorphismProperty Scheme.{u}) := sorry

/-- In a commutative triangle `f ≫ q = p`, smoothness descends from `p` to `q` when `f` is
surjective, flat, and locally of finite presentation. -/
theorem of_comp_eq_of_fppf {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] [Smooth p]
    (hcomm : f ≫ q = p) : Smooth q := sorry

/-- If `f` is a surjective smooth morphism, `f ≫ q` is smooth, and `q` is locally of finite
presentation, then `q` is smooth. -/
theorem of_comp_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
    [Surjective f] (hf : Smooth f) (hfq : Smooth (f ≫ q))
    (hq : LocallyOfFinitePresentation q) : Smooth q := sorry

/-- In a commutative triangle `f ≫ q = p`, smoothness descends from `p` to `q`
along a surjective smooth morphism `f`. -/
theorem of_comp_eq_of_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S)
    (q : Y ⟶ S) [Surjective f] [Smooth f] [Smooth p] (hcomm : f ≫ q = p) :
    Smooth q := sorry

end AlgebraicGeometry.Smooth

namespace AlgebraicGeometry.Scheme.Hom

/-- Smoothness at a point over a field descends along a morphism that is flat at that point. -/
theorem smoothAt_of_comp_of_flatAt
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType (f ≫ g)] [LocallyOfFiniteType g]
    (x : X) (hsmooth : (f ≫ g).SmoothAt x) (hflat : flatAt f x) :
    g.SmoothAt (f x) := sorry

/-- Smoothness over a field descends along a flat surjective morphism. -/
theorem smooth_of_comp_of_flat_of_surjective
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType g] [Flat f] [Surjective f] [Smooth (f ≫ g)] :
    Smooth g := sorry

end AlgebraicGeometry.Scheme.Hom
