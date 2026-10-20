/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Order.RelSeries
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveAtlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap82.Lemma_82_25_1_ChowPullback

/-!
# Projective splitting data for Chow groups of algebraic spaces

This module records the algebraic-space projective morphism class, invertible-quotient
filtrations of modules, and universal injectivity of Chow pullback used by the splitting
principle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is projective when it admits a closed-immersion
presentation in the projective atlas of a finite-type quasi-coherent module on its
target. -/
class Projective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- A finite-type quasi-coherent projective-atlas presentation of `f`. -/
  exists_presentation :
    ∃ (E : Y.Modules) (hE : E.IsQuasicoherent) (hFT : E.IsFiniteType)
      (i : X ⟶ @ProjectiveAtlas.space S Y E hE),
      IsClosedImmersion i ∧ i ≫ @ProjectiveAtlas.projection S Y E hE = f

/-- Projectivity is equivalent to the existence of a closed immersion into a projective
atlas of a finite-type quasi-coherent module whose composite is the given morphism. -/
theorem projective_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Projective f ↔
      ∃ (E : Y.Modules) (hE : E.IsQuasicoherent) (hFT : E.IsFiniteType)
        (i : X ⟶ @ProjectiveAtlas.space S Y E hE),
        IsClosedImmersion i ∧ i ≫ @ProjectiveAtlas.projection S Y E hE = f :=
  sorry

/-- The structure projection of a projective atlas of a finite-type quasi-coherent
module is projective. -/
instance instProjective_projection {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : X.Modules) [E.IsQuasicoherent] [E.IsFiniteType] :
    Projective (ProjectiveAtlas.projection E) where
  exists_presentation :=
    ⟨E, inferInstance, inferInstance, 𝟙 _, inferInstance,
      Category.id_comp (ProjectiveAtlas.projection E)⟩

namespace Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Adjacent subobjects of an `𝒪_X`-module whose cokernel is invertible. -/
def invertibleQuotientRel (E : X.Modules) (F G : Subobject E) : Prop :=
  ∃ (hFG : F ≤ G), isInvertibleObject (cokernel (Subobject.ofLE F G hFG))

/-- An `𝒪_X`-module has an invertible-quotient filtration if it admits a finite
`RelSeries` of subobjects from `⊥` to `⊤` whose successive cokernels are invertible. -/
def HasInvertibleQuotientFiltration (E : X.Modules) : Prop :=
  ∃ s : RelSeries (setOf fun p : Subobject E × Subobject E ↦ invertibleQuotientRel E p.1 p.2),
    s.head = ⊥ ∧ s.last = ⊤

/-- An `𝒪_X`-module has an invertible-quotient filtration of length `r` if it admits a
`RelSeries` of that length from `⊥` to `⊤` whose successive cokernels are invertible. -/
def HasInvertibleQuotientFiltrationOfLength (r : ℕ) (E : X.Modules) : Prop :=
  ∃ s : RelSeries (setOf fun p : Subobject E × Subobject E ↦ invertibleQuotientRel E p.1 p.2),
    s.length = r ∧ s.head = ⊥ ∧ s.last = ⊤

/-- A prescribed-length invertible-quotient filtration is exactly a `RelSeries` of that
length from `⊥` to `⊤` with invertible successive cokernels. -/
theorem hasInvertibleQuotientFiltrationOfLength_iff (r : ℕ) (E : X.Modules) :
    HasInvertibleQuotientFiltrationOfLength r E ↔
      ∃ s : RelSeries (setOf fun p : Subobject E × Subobject E ↦ invertibleQuotientRel E p.1 p.2),
        s.length = r ∧ s.head = ⊥ ∧ s.last = ⊤ :=
  sorry

/-- Forgetting the length of a prescribed invertible-quotient filtration yields an
invertible-quotient filtration. -/
theorem HasInvertibleQuotientFiltrationOfLength.toHasInvertibleQuotientFiltration
    {r : ℕ} {E : X.Modules} (h : HasInvertibleQuotientFiltrationOfLength r E) :
    HasInvertibleQuotientFiltration E :=
  sorry

end Modules

namespace Hom

/-- A flat morphism of relative dimension `d` between good algebraic spaces over `B` has
universally injective Chow pullback if after every morphism of good algebraic spaces over
`B` the induced flat pullback is injective in every degree. -/
def UniversallyInjectivePullback {S : Scheme.{u}} {B X P : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (π : P ⟶ X) (d : ℕ) [Flat π] [RelativeDimension π d]
    [QuasiSeparated (π ≫ pX)] [LocallyOfFiniteType (π ≫ pX)] : Prop :=
  ∀ {Y : AlgebraicSpace S} (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (g : Y ⟶ X) (hg : g ≫ pX = pY) [Flat (pullback.fst g π)]
    [RelativeDimension (pullback.fst g π) d]
    [QuasiSeparated (pullback.fst g π ≫ pY)]
    [LocallyOfFiniteType (pullback.fst g π ≫ pY)] (k : ℤ),
    Function.Injective
      (chowFlatPullback pY (pullback.fst g π ≫ pY) δ (pullback.fst g π) d rfl k)

/-- Universal Chow-pullback injectivity specializes to a chosen good morphism over `B`
and a chosen degree. -/
theorem UniversallyInjectivePullback.injective {S : Scheme.{u}}
    {B X P : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (π : P ⟶ X) (d : ℕ) [Flat π] [RelativeDimension π d]
    [QuasiSeparated (π ≫ pX)] [LocallyOfFiniteType (π ≫ pX)]
    (hπ : UniversallyInjectivePullback pX δ π d)
    {Y : AlgebraicSpace S} (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (g : Y ⟶ X) (hg : g ≫ pX = pY) [Flat (pullback.fst g π)]
    [RelativeDimension (pullback.fst g π) d]
    [QuasiSeparated (pullback.fst g π ≫ pY)]
    [LocallyOfFiniteType (pullback.fst g π ≫ pY)] (k : ℤ) :
    Function.Injective
      (chowFlatPullback pY (pullback.fst g π ≫ pY) δ (pullback.fst g π) d rfl k) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
