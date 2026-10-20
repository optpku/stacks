/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Fiber

/-!
# Finiteness and quasi-finiteness over generic points

This file relates finite point-set fibers over generic points to finite restrictions on affine
neighborhoods and relates quasi-finiteness along such fibers to the generic points of irreducible
components of the source.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a locally finite type morphism and a generic point `η` of the target, the point-set fiber
over `η` consists of generic points of the source if and only if the morphism is quasi-finite at
every point of that fiber, equivalently at every generic point in that fiber. -/
theorem tfae_fiber_subset_genericPoints_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] {η : Y}
    (hη : η ∈ genericPoints Y) :
    List.TFAE
      [ (∀ x : X, f x = η → x ∈ genericPoints X)
      , (∀ x : X, f x = η → f.QuasiFiniteAt x)
      , (∀ x : X, x ∈ genericPoints X → f x = η → f.QuasiFiniteAt x)
      ] := sorry

/-- For a locally finite type morphism and a generic point `η` of the target, the point-set fiber
over `η` is finite if and only if finitely many affine opens cover that fiber and have finite
restrictions to a common affine neighborhood of `η`. -/
theorem tfae_finiteFiber_finiteAffineCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] {η : Y}
    (hη : η ∈ genericPoints Y) :
    List.TFAE
      [ ({x : X | f x = η} : Set X).Finite
      , (∃ (n : ℕ) (U : Fin n → X.Opens) (V : Y.Opens)
            (_ : IsAffineOpen V) (_ : ∀ i, IsAffineOpen (U i)) (_ : η ∈ V)
            (hUV : ∀ i, U i ≤ f ⁻¹ᵁ V)
            (_ : ∀ x : X, f x = η → ∃ i : Fin n, x ∈ U i),
          ∀ i, IsFinite (f.resLE V (U i) (hUV i)))
      ] := sorry

/-- For a locally finite type quasi-separated morphism and a generic point `η` of the target,
finiteness of the point-set fiber over `η` is equivalent to the finite affine-cover criterion and
to the existence of one affine source neighborhood of the fiber whose restriction to an affine
target neighborhood of `η` is finite. -/
theorem tfae_finiteFiber_finiteAffineOpen_of_quasiSeparated
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiSeparated f] {η : Y}
    (hη : η ∈ genericPoints Y) :
    List.TFAE
      [ ({x : X | f x = η} : Set X).Finite
      , (∃ (n : ℕ) (U : Fin n → X.Opens) (V : Y.Opens)
            (_ : IsAffineOpen V) (_ : ∀ i, IsAffineOpen (U i)) (_ : η ∈ V)
            (hUV : ∀ i, U i ≤ f ⁻¹ᵁ V)
            (_ : ∀ x : X, f x = η → ∃ i : Fin n, x ∈ U i),
          ∀ i, IsFinite (f.resLE V (U i) (hUV i)))
      , (∃ (U : X.Opens) (V : Y.Opens)
            (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : η ∈ V)
            (hUV : U ≤ f ⁻¹ᵁ V) (_ : ∀ x : X, f x = η → x ∈ U),
          IsFinite (f.resLE V U hUV))
      ] := sorry

/-- For a locally finite type, quasi-compact, quasi-separated morphism and a generic point `η` of
the target, finiteness of the point-set fiber over `η` is equivalent to the finite affine-cover
and one-affine-open criteria, and to finiteness over the inverse image of some affine target
neighborhood of `η`. -/
theorem tfae_finiteFiber_finiteRestriction_of_quasiCompact_quasiSeparated
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f]
    {η : Y} (hη : η ∈ genericPoints Y) :
    List.TFAE
      [ ({x : X | f x = η} : Set X).Finite
      , (∃ (n : ℕ) (U : Fin n → X.Opens) (V : Y.Opens)
            (_ : IsAffineOpen V) (_ : ∀ i, IsAffineOpen (U i)) (_ : η ∈ V)
            (hUV : ∀ i, U i ≤ f ⁻¹ᵁ V)
            (_ : ∀ x : X, f x = η → ∃ i : Fin n, x ∈ U i),
          ∀ i, IsFinite (f.resLE V (U i) (hUV i)))
      , (∃ (U : X.Opens) (V : Y.Opens)
            (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : η ∈ V)
            (hUV : U ≤ f ⁻¹ᵁ V) (_ : ∀ x : X, f x = η → x ∈ U),
          IsFinite (f.resLE V U hUV))
      , (∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : η ∈ V), IsFinite (f ∣_ V))
      ] := sorry

/-- A quasi-compact, quasi-separated, locally finite type morphism with finite point-set fiber
over a generic point of an irreducible component of the target is finite over an open
neighborhood of that point. -/
theorem exists_isFinite_morphismRestrict_of_finiteFiber_at_genericPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiSeparated f] {η : Y} (hη : η ∈ genericPoints Y)
    (hfiber : ({x : X | f x = η} : Set X).Finite) :
    ∃ V : Y.Opens, η ∈ V ∧ IsFinite (f ∣_ V) := sorry

end AlgebraicGeometry.Scheme.Hom
