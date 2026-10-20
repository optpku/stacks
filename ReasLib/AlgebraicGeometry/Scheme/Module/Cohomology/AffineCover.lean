/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Lattice.Nat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Acyclicity
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.MayerVietoris
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AffineOpenCover

variable {X : Scheme.{u}}

/-- `HasCard X t` means that `X` has an affine open cover indexed by `Fin t`. -/
def HasCard (X : Scheme.{u}) (t : ℕ) : Prop :=
  ∃ 𝒰 : Fin t → X.Opens, IsOpenCover 𝒰 ∧ ∀ i, IsAffineOpen (𝒰 i)

/-- `HasCard X t` is equivalently an affine-open-cover bundle whose index type is equivalent to
`Fin t`. -/
theorem hasCard_iff_nonempty (X : Scheme.{u}) (t : ℕ) :
    HasCard X t ↔ ∃ 𝒰 : X.AffineOpenCover, Nonempty (𝒰.I₀ ≃ Fin t) := sorry

/-- A quasi-compact scheme has an affine open cover indexed by some finite type. -/
theorem exists_hasCard (X : Scheme.{u}) [CompactSpace X] : ∃ t, HasCard X t := sorry

/-- Stacks 01XI: the minimal number of affine opens in a cover of `X`. -/
@[stacks 01XI] def number (X : Scheme.{u}) : ℕ := sInf {t | HasCard X t}

/-- On a quasi-compact scheme, the minimal affine-cover number is attained. -/
theorem number_hasCard (X : Scheme.{u}) [CompactSpace X] : HasCard X (number X) := sorry

/-- Every affine-open-cover cardinality bounds the minimal affine-cover number. -/
theorem number_le {X : Scheme.{u}} {t : ℕ} (ht : HasCard X t) : number X ≤ t := sorry

/-- The affine-cover number is the least cardinality of an affine open cover. -/
theorem number_isLeast (X : Scheme.{u}) [CompactSpace X] :
    IsLeast {t | HasCard X t} (number X) := sorry

/-- A finite affine open cover bounds the degree in which global cohomology of a
quasi-coherent module vanishes when the diagonal is affine. -/
theorem globalCohomology_isZero_of_cover
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (t : ℕ) (𝒰 : Fin t → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (hAffine : ∀ i, IsAffineOpen (𝒰 i))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (n : ℕ) (hn : t ≤ n) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' n (⊤ : Opens X)) := sorry

/-- The affine-cover cardinality of `X` bounds the vanishing degree of global cohomology. -/
theorem globalCohomology_isZero_of_hasCard
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    {t : ℕ} (ht : HasCard X t)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (n : ℕ) (hn : t ≤ n) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' n (⊤ : Opens X)) := sorry

/-- Stacks 01XI: on a quasi-compact scheme with affine diagonal, global cohomology of every
quasi-coherent module vanishes in degrees at least `number X`. -/
@[stacks 01XI] theorem globalCohomology_isZero_of_number
    (X : Scheme.{u}) [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (n : ℕ) (hn : number X ≤ n) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' n (⊤ : Opens X)) := sorry

/-- Stacks 071L: the maximal intersection-wise affine-cover bound for a finite open cover. -/
@[stacks 071L] def cohomologyBound {m : ℕ} (U : Fin m → X.Opens) : ℕ :=
  Finset.univ.sup (fun I : Finset (Fin m) ↦
    I.card + number ((I.inf U : X.Opens) : Scheme) - 1)

/-- Stacks 071L: on a quasi-compact quasi-separated scheme, global cohomology of every
quasi-coherent module vanishes in degrees at least the finite-cover intersection bound. -/
@[stacks 071L] theorem globalCohomology_isZero_of_finiteCover
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {m : ℕ} (U : Fin m → X.Opens) (hcover : IsOpenCover U)
    (hUcompact : ∀ i, CompactSpace (U i : Scheme))
    (hUseparated : ∀ i, (U i : Scheme).IsSeparated)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ) (hp : cohomologyBound U ≤ p) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' p (⊤ : Opens X)) := sorry

end AlgebraicGeometry.Scheme.AffineOpenCover
