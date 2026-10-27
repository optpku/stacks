/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Graph

/-!
# Open representability of the graph transformation

The graph transformation from relative morphisms to the Hilbert functor is
representable by open immersions. A Hilbert point is a graph precisely when
its restricted first projection is an isomorphism.
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Z B X : AlgebraicSpace S}

/-- The two maps `Y ⟶ T` and `Y ⟶ Z` from a Hilbert point agree over `B`. -/
private theorem fstRestrict_lift_condition {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemeOver B}
    (p : FiberPoint z x σ) :
    p.structureMap ≫ σ.hom =
      (p.subspace.ι ≫ pullback.fst (productHom z x) σ.hom ≫ pullback.fst z x) ≫ z := sorry

/-- The first-projection restriction `pr₁|_Y : Y ⟶ Z_T` of a Hilbert point. -/
def fstRestrict {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemeOver B}
    (p : FiberPoint z x σ) : p.subspace.X ⟶ pullback σ.hom z :=
  pullback.lift p.structureMap
    (p.subspace.ι ≫ pullback.fst (productHom z x) σ.hom ≫ pullback.fst z x)
    (fstRestrict_lift_condition p)

/-- The composite of the restricted first projection with `Z_T ⟶ T` is the
inclusion of `Y` followed by the product fibre's projection to `T`. -/
theorem fstRestrict_fst {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemeOver B}
    (p : FiberPoint z x σ) :
    fstRestrict p ≫ pullback.fst σ.hom z =
      p.subspace.ι ≫ pullback.snd (productHom z x) σ.hom := sorry

/-- The composite of the restricted first projection with `Z_T ⟶ Z` is the
inclusion of `Y` followed by the projections of the product fibre to `Z`. -/
theorem fstRestrict_snd {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemeOver B}
    (p : FiberPoint z x σ) :
    fstRestrict p ≫ pullback.snd σ.hom z =
      p.subspace.ι ≫ pullback.fst (productHom z x) σ.hom ≫ pullback.fst z x := sorry

/-- The structure morphism of a Hilbert point factors through the restricted
first projection followed by `Z_T ⟶ T`. -/
theorem fstRestrict_comp_structureMap {z : Z ⟶ B} {x : X ⟶ B} {σ : SchemeOver B}
    (p : FiberPoint z x σ) :
    fstRestrict p ≫ pullback.fst σ.hom z = p.structureMap := sorry

/-- A Hilbert point has an open locus in the test scheme characterized by
invertibility of its restricted first projection after every base change. -/
theorem exists_opens_isIso_fstRestrict_iff (z : Z ⟶ B) (x : X ⟶ B) [Separated x]
    [FinitePresentation z] [Flat z] [Proper z]
    (σ : SchemeOver B) (p : FiberPoint z x σ) :
    ∃ V : (σ.left.left).Opens,
      ∀ {τ : SchemeOver B} (h : τ ⟶ σ),
        Nonempty (Over.mk h.left.left ⟶ Over.mk V.ι) ↔
          IsIso (fstRestrict (p.pullback h)) := sorry

/-- A Hilbert point has invertible restricted first projection if and only if
it represents the graph of a relative morphism. -/
theorem isIso_fstRestrict_iff_exists_graphPoint (z : Z ⟶ B) (x : X ⟶ B)
    [Separated x] [FinitePresentation z] [Flat z] [Proper z]
    (σ : SchemeOver B) (p : FiberPoint z x σ) :
    IsIso (fstRestrict p) ↔
      ∃ b : BaseChangeMorphism z x σ.hom, Rel p (graphPoint z x σ b) := sorry

/-- For separated `X ⟶ B` and finitely presented, flat, proper `Z ⟶ B`, the
graph transformation `Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B}` is representable by
open immersions of schemes. -/
theorem graph_isOpenImmersion (z : Z ⟶ B) (x : X ⟶ B) [Separated x]
    [FinitePresentation z] [Flat z] [Proper z] :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (fun _ _ h ↦ AlgebraicGeometry.IsOpenImmersion h.left.left :
        MorphismProperty (SchemeOver B)) (graph z x) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
