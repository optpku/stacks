/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalAcyclicity
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

@[expose] public section

universe u v

namespace AlgebraicGeometry.Scheme

open EtaleVanishingCycles

/-- Local acyclicity at a geometric point relative to derived étale coefficients is preserved
by a cartesian base change along a locally quasi-finite morphism locally of finite type. -/
theorem locallyAcyclicAt_baseChange_of_locallyQuasiFinite
    {X X' S S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g)
    (K : Complexes X) (xbar' : GeometricPoint X')
    [LocallyOfFiniteType g] [LocallyQuasiFinite g]
    (h : LocallyAcyclicAt f (xbar'.map g') K) :
    LocallyAcyclicAt f' xbar' ((derivedInverseImage g').obj K) := sorry

/-- Local acyclicity at a geometric point relative to derived étale coefficients is preserved
by a cartesian base change along a directed inverse limit of locally quasi-finite morphisms
locally of finite type with affine transition morphisms. -/
theorem locallyAcyclicAt_baseChange_of_affineTransitionLimit
    {X X' S S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g)
    (K : Complexes X) (xbar' : GeometricPoint X')
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (e : c.pt ≅ S')
    (he : ∀ i : OrderDual I, c.π.app i ≫ t.app i = e.hom ≫ g)
    [∀ i : OrderDual I, LocallyOfFiniteType (t.app i)]
    [∀ i : OrderDual I, LocallyQuasiFinite (t.app i)]
    [∀ {i j : OrderDual I} (q : i ⟶ j), IsAffineHom (D.map q)]
    (h : LocallyAcyclicAt f (xbar'.map g') K) :
    LocallyAcyclicAt f' xbar' ((derivedInverseImage g').obj K) := sorry

/-- Local acyclicity at a geometric point relative to derived étale coefficients is preserved
by a cartesian base change along an integral morphism. -/
theorem locallyAcyclicAt_baseChange_of_integral
    {X X' S S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g)
    (K : Complexes X) (xbar' : GeometricPoint X')
    [IsIntegralHom g]
    (h : LocallyAcyclicAt f (xbar'.map g') K) :
    LocallyAcyclicAt f' xbar' ((derivedInverseImage g').obj K) := sorry

end AlgebraicGeometry.Scheme
