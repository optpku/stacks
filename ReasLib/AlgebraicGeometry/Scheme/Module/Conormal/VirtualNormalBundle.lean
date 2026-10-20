/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.OpenRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive

/-!
# Virtual normal bundles of immersions

A virtual normal bundle consists of a finite locally free module together with a quotient of
its dual onto the conormal sheaf of an immersion. Such data transports across a factorization
as a closed immersion followed by an open immersion.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A virtual normal bundle for an immersion `i : Z ⟶ X` consists of a finite locally free
`Z`-module whose dual surjects onto the conormal sheaf of `i`. -/
structure VirtualNormalBundle {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    Type (u + 1) where
  /-- The finite locally free module underlying the virtual normal bundle. -/
  module : Z.Modules
  /-- The underlying module is finite locally free. -/
  isFiniteLocallyFree : Scheme.Modules.IsFiniteLocallyFree module
  /-- The chosen morphism from the dual module onto the conormal sheaf. -/
  map : Scheme.Modules.dual module ⟶ conormalSheaf i
  /-- The chosen morphism is an epimorphism. -/
  map_epi : Epi map

namespace VirtualNormalBundle

/-- Construct a virtual normal bundle from an explicit finite locally free module and
epimorphism from its dual to the conormal sheaf. -/
def ofSurjection {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (N : Z.Modules) (hN : Scheme.Modules.IsFiniteLocallyFree N)
    (sigma : Scheme.Modules.dual N ⟶ conormalSheaf i) (hsigma : Epi sigma) :
    VirtualNormalBundle i where
  module := N
  isFiniteLocallyFree := hN
  map := sigma
  map_epi := hsigma

/-- The finite-local-freeness and epimorphism conditions defining a virtual normal bundle. -/
theorem spec {Z X : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i]
    (V : VirtualNormalBundle i) :
    Scheme.Modules.IsFiniteLocallyFree V.module ∧ Epi V.map := sorry

/-- Composing with the conormal comparison for a closed-then-open factorization preserves
epimorphy. -/
theorem factorizationMap_epi {Z U X : Scheme.{u}} (i : Z ⟶ X)
    (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsImmersion i] [IsClosedImmersion j] [IsOpenImmersion k]
    (V : VirtualNormalBundle i) :
    Epi (V.map ≫ Conormal.factorizationConormalComparison i j k h) := sorry

/-- Regard a virtual normal bundle as one for the closed part of a closed-then-open
factorization. -/
def forFactorization {Z U X : Scheme.{u}} (i : Z ⟶ X)
    (j : Z ⟶ U) (k : U ⟶ X) (h : j ≫ k = i)
    [IsImmersion i] [IsClosedImmersion j] [IsOpenImmersion k]
    (V : VirtualNormalBundle i) : VirtualNormalBundle j where
  module := V.module
  isFiniteLocallyFree := V.isFiniteLocallyFree
  map := V.map ≫ Conormal.factorizationConormalComparison i j k h
  map_epi := factorizationMap_epi i j k h V

/-- Regard a virtual normal bundle on an immersion as one on its canonical closed-immersion
factor through the coborder range. -/
def toCoborder {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (V : VirtualNormalBundle i) : VirtualNormalBundle i.liftCoborder :=
  forFactorization i i.liftCoborder i.coborderRange.ι i.liftCoborder_ι V

end VirtualNormalBundle
end AlgebraicGeometry.Scheme.Hom
