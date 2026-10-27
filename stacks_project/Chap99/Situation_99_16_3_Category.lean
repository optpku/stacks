/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.LeftDerived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction

/-! # Compatibility for admissible fibre complexes with chart parameters -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The canonical induced map on fibres of a morphism of test schemes. -/
abbrev fiberMap (f : X ⟶ B) {σ τ : SchemeOver B} (h : σ ⟶ τ) :
    pullback f σ.hom ⟶ pullback f τ.hom := CohStack.fiberMap f h

/-- The induced fibre map commutes with projection to the fixed space. -/
theorem fiberMap_fst (f : X ⟶ B) {σ τ : SchemeOver B} (h : σ ⟶ τ) :
    fiberMap f h ≫ pullback.fst f τ.hom = pullback.fst f σ.hom :=
  CohStack.fiberMap_fst f h

/-- The induced fibre map commutes with projection to the test scheme. -/
theorem fiberMap_snd (f : X ⟶ B) {σ τ : SchemeOver B} (h : σ ⟶ τ) :
    fiberMap f h ≫ pullback.snd f τ.hom =
      pullback.snd f σ.hom ≫ (ofOverFunctor S).map h.left :=
  CohStack.fiberMap_snd f h

/-- The identity test-scheme morphism induces the identity fibre map. -/
theorem fiberMap_id_eq (f : X ⟶ B) (σ : SchemeOver B) :
    fiberMap f (𝟙 σ) = 𝟙 (pullback f σ.hom) := CohStack.fiberMap_id_eq f σ

/-- The fibre map of a composite is the composite of the induced fibre maps. -/
theorem fiberMap_comp_eq (f : X ⟶ B) {σ τ ρ : SchemeOver B}
    (h : σ ⟶ τ) (k : τ ⟶ ρ) :
    fiberMap f (h ≫ k) = fiberMap f h ≫ fiberMap f k := CohStack.fiberMap_comp_eq f h k

/-- The carrier of the category of admissible complexes, with historical chart parameters. -/
abbrev Obj (f : X ⟶ B)
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f] : Type (u + 1) := category f

/-- Package a test scheme and an admissible complex on the fibre as an object of
`Obj f`. -/
def of {f : X ⟶ B}
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f] (σ : SchemeOver B)
    (complex : ModuleDerived (pullback f σ.hom))
    (isPerfectRelative :
      ModuleDerived.IsPerfectRelativeTo (pullback.snd f σ.hom) complex)
    (fiberNegativeSelfExtVanish :
      ∀ t : FieldValuedPoint (ofOver σ.left),
        ModuleDerived.fiberNegativeExtVanish (pullback.snd f σ.hom) complex complex t) :
    Obj f :=
  Object.of σ complex isPerfectRelative fiberNegativeSelfExtVanish

/-- Build a morphism of `Obj f` from a morphism of schemes over `B` and a
derived-category isomorphism along the induced fibre map. -/
def homMk {f : X ⟶ B}
    [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (pullback.snd f σ.hom),
      (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
    [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (pullback.snd f σ.hom),
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
      DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
    [Proper f] [Flat f] [FinitePresentation f] {x y : (@Obj S X B f chartDerived chartTensor _ _ _)}
    (base : x.σ ⟶ y.σ)
    (iso : (ModuleDerived.pullback (fiberMap f base)).obj y.complex ≅ x.complex) :
    x ⟶ y := Hom.of (x := x) (y := y) base iso

end AlgebraicGeometry.AlgebraicSpace.Complexes
