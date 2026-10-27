/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Elements
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import ReasLib.RingTheory.AdicCompletion.AtPrime
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Factorization
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Basic

/-!
# Open-closed coproducts and characteristic groupoids

For a Noetherian ring `Λ` and a maximal ideal `m`, the coproduct of the
punctured spectrum `Spec(Λ) \ {m}` with `Spec(C)` folds to `Spec(Λ)`. The
associated characteristic groupoid and the canonical formal object over the
completed local ring `Λ_m^∧` are constructed from a finite-type factorization
`Λ → C → Λ_m^∧`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open FiberedCategoryOver
open AlgebraicGeometry.GroupoidsOver.Factorization
open IsLocalRing PrimeSpectrum
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]

/-- The open complement `U = Spec(Λ) \ {m}` of a closed maximal point. -/
def puncturedOpen (m : MaximalSpectrum Λ) :
    (Spec (CommRingCat.of Λ)).Opens :=
  ⟨({m.toPrimeSpectrum} : Set (Spec (CommRingCat.of Λ)))ᶜ,
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal m.toPrimeSpectrum).2
      m.isMaximal).isOpen_compl⟩

/-- A prime lies in `puncturedOpen m` if and only if it is not the closed
point `m`. -/
theorem mem_puncturedOpen_iff_ne_closedPoint (m : MaximalSpectrum Λ)
    (p : PrimeSpectrum Λ) :
    p ∈ puncturedOpen m ↔ p ≠ m.toPrimeSpectrum := by
  rfl

/-- The coproduct scheme `S' = U ⨿ Spec(C)`. -/
def coproduct (m : MaximalSpectrum Λ) (C : Type u) [CommRing C] :
    Scheme.{u} :=
  (puncturedOpen m).toScheme ⨿ Spec (CommRingCat.of C)

/-- The fold `S' ⟶ Spec(Λ)` of the open immersion `U ⟶ Spec(Λ)` and
`Spec(C) ⟶ Spec(Λ)`. -/
def coproductToS (m : MaximalSpectrum Λ) (C : Type u) [CommRing C]
    [Algebra Λ C] :
    coproduct m C ⟶ Spec (CommRingCat.of Λ) :=
  coprod.desc (puncturedOpen m).ι
    (Spec.map (CommRingCat.ofHom (algebraMap Λ C)))

/-- The left summand of `coproductToS` is the open immersion of
`puncturedOpen m`. -/
theorem coproductToS_inl (m : MaximalSpectrum Λ) (C : Type u) [CommRing C]
    [Algebra Λ C] :
    coprod.inl ≫ coproductToS m C = (puncturedOpen m).ι := by
  exact coprod.inl_desc _ _

/-- The right summand of `coproductToS` is `Spec` of the structure map
`Λ → C`. -/
theorem coproductToS_inr (m : MaximalSpectrum Λ) (C : Type u) [CommRing C]
    [Algebra Λ C] :
    coprod.inr ≫ coproductToS m C =
      Spec.map (CommRingCat.ofHom (algebraMap Λ C)) := by
  exact coprod.inr_desc _ _

/-- The category fibred in groupoids associated to factoring through
`U ⨿ Spec(C) ⟶ Spec(Λ)`. -/
def groupoids (m : MaximalSpectrum Λ) (C : Type u) [CommRing C]
    [Algebra Λ C] :
    GroupoidsOver (Spec (CommRingCat.of Λ)) :=
  toGroupoids (coproductToS m C)

/-- The projection of `groupoids m C` is the opposite category-of-elements
projection of the characteristic functor of `coproductToS m C`. -/
theorem groupoids_p (m : MaximalSpectrum Λ) (C : Type u) [CommRing C]
    [Algebra Λ C] :
    (groupoids m C).p =
      ((Sets.ofPresheaf (Over (Spec (CommRingCat.of Λ)))).obj
        (factorsThroughFunctor (coproductToS m C))).p := by
  rfl

/-- The residue morphism `Spec(κ(Λ_m^∧)) ⟶ Spec(Λ)` is locally of finite type. -/
theorem completedLocalRing_residue_locallyOfFiniteType (m : MaximalSpectrum Λ) :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk
            (maximalIdeal (CompletedLocalRing m.toPrimeSpectrum)))) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Λ (CompletedLocalRing m.toPrimeSpectrum)))) := by
  letI : m.toPrimeSpectrum.asIdeal.IsMaximal := m.isMaximal
  let A := Localization.AtPrime m.toPrimeSpectrum.asIdeal
  let R := CompletedLocalRing m.toPrimeSpectrum
  have hA : Function.Surjective (algebraMap Λ (ResidueField A)) :=
    Ideal.algebraMap_residueField_surjective m.toPrimeSpectrum.asIdeal
  have hR : Function.Surjective (ResidueField.map (algebraMap A R)) :=
    (AdicCompletion.residueField_map_bijective A).2
  have hcomp : (ResidueField.map (algebraMap A R)).comp
      (algebraMap Λ (ResidueField A)) = (residue R).comp (algebraMap Λ R) := by
    ext a
    change ResidueField.map (algebraMap A R) (residue A (algebraMap Λ A a)) =
      residue R (algebraMap Λ R a)
    rw [ResidueField.map_residue, IsScalarTower.algebraMap_apply Λ A R]
  have hsurj : Function.Surjective ((residue R).comp (algebraMap Λ R)) := by
    rw [← hcomp]
    exact hR.comp hA
  rw [← Spec.map_comp]
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
  exact RingHom.FiniteType.of_surjective _ hsurj

/-- The completed local ring `Λ_m^∧` as a complete local `Spec(Λ)`-algebra. -/
def completeLocalSAlgebra (m : MaximalSpectrum Λ) :
    CompleteLocalSAlgebra (Spec (CommRingCat.of Λ)) :=
  CompleteLocalSAlgebra.of (CompletedLocalRing m.toPrimeSpectrum)
    (Spec.map (CommRingCat.ofHom
      (algebraMap Λ (CompletedLocalRing m.toPrimeSpectrum))))
    (completedLocalRing_residue_locallyOfFiniteType m)

/-- `completeLocalSAlgebra m` recovers the completed local ring and the
structure morphism `Spec(Λ_m^∧) ⟶ Spec(Λ)`. -/
theorem completeLocalSAlgebra_spec (m : MaximalSpectrum Λ) :
    (completeLocalSAlgebra m).carrier =
      CompletedLocalRing m.toPrimeSpectrum ∧
      (completeLocalSAlgebra m).toS =
        Spec.map (CommRingCat.ofHom
          (algebraMap Λ (CompletedLocalRing m.toPrimeSpectrum))) := by
  exact ⟨rfl, rfl⟩

variable {C : Type u} [CommRing C] [Algebra Λ C] [Algebra.FiniteType Λ C]

/-- The truncation morphism `Spec(R ⧸ m_R^{n+1}) ⟶ Spec(C)` induced by
`φ : C → Λ_m^∧`. -/
def truncationToSpecC (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (completeLocalSAlgebra m).truncationSpec n ⟶ Spec (CommRingCat.of C) :=
  Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk
        (maximalIdeal (CompletedLocalRing m.toPrimeSpectrum) ^ (n + 1)))) ≫
    Spec.map (CommRingCat.ofHom φ.toRingHom)

/-- The truncation morphism `Spec(R ⧸ m_R^{n+1}) ⟶ S'` through the `Spec(C)`
summand. -/
def truncationToCoproduct (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (completeLocalSAlgebra m).truncationSpec n ⟶ coproduct m C :=
  truncationToSpecC m φ n ≫ coprod.inr

/-- The object of `Over Spec(Λ)` whose structure morphism factors through
`S'` via the `Spec(C)` summand. -/
def truncationOver (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    Over (Spec (CommRingCat.of Λ)) :=
  Over.mk (truncationToCoproduct m φ n ≫ coproductToS m C)

/-- The Over morphism exhibiting the truncation as factoring through `S'`. -/
def truncationOverHom (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    truncationOver m φ n ⟶ Over.mk (coproductToS m C) :=
  Over.homMk (truncationToCoproduct m φ n) rfl

/-- `truncationOverHom` is `Over.homMk` of `truncationToCoproduct`. -/
theorem truncationOverHom_left (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (truncationOverHom m φ n).left = truncationToCoproduct m φ n := by
  rfl

/-- The characteristic-functor value of a truncation, given by the `Spec(C)`
factorization. -/
def truncationValue (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (factorsThroughFunctor (coproductToS m C)).obj
      (Opposite.op (truncationOver m φ n)) :=
  ⟨⟨⟨truncationOverHom m φ n⟩⟩⟩

/-- The category-of-elements object of a truncation. -/
def truncationElement (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (factorsThroughFunctor (coproductToS m C)).Elements :=
  ⟨Opposite.op (truncationOver m φ n), truncationValue m φ n⟩

/-- The total-category object of `groupoids m C` over the `n`th truncation. -/
def truncationObject (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (groupoids m C).total :=
  Opposite.op (truncationElement m φ n)

private theorem truncationToCoproduct_comp_coproductToS (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    truncationToCoproduct m φ n ≫ coproductToS m C =
      (completeLocalSAlgebra m).truncationToS n := by
  have hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ C)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap Λ (CompletedLocalRing m.toPrimeSpectrum))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact φ.comp_algebraMap
  change (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (maximalIdeal (CompletedLocalRing m.toPrimeSpectrum) ^ (n + 1)))) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ coprod.inr) ≫ coproductToS m C =
    Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (maximalIdeal (CompletedLocalRing m.toPrimeSpectrum) ^ (n + 1)))) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap Λ (CompletedLocalRing m.toPrimeSpectrum)))
  rw [Category.assoc, Category.assoc, coproductToS_inr, hφ]

/-- Successive truncations remain compatible with the fold to `Spec(Λ)` after
composing with `truncationToCoproduct`. -/
theorem truncationStage_triangle (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (completeLocalSAlgebra m).truncationMap n ≫
        (truncationOver m φ (n + 1)).hom =
      (truncationOver m φ n).hom := by
  change (completeLocalSAlgebra m).truncationMap n ≫
      (truncationToCoproduct m φ (n + 1) ≫ coproductToS m C) =
    truncationToCoproduct m φ n ≫ coproductToS m C
  rw [truncationToCoproduct_comp_coproductToS, truncationToCoproduct_comp_coproductToS]
  exact (completeLocalSAlgebra m).stageToS_comp n

/-- The Over morphism of successive truncations over `Spec(Λ)`. -/
def truncationStageHom (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    truncationOver m φ n ⟶ truncationOver m φ (n + 1) :=
  Over.homMk ((completeLocalSAlgebra m).truncationMap n)
    (truncationStage_triangle m φ n)

/-- The underlying scheme morphism of `truncationStageHom` is the truncation
thickening. -/
theorem truncationStageHom_left (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (truncationStageHom m φ n).left =
      (completeLocalSAlgebra m).truncationMap n := by
  rfl

/-- Characteristic-functor values of successive truncations are compatible with
the truncation thickening. -/
theorem truncationValue_natural (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (factorsThroughFunctor (coproductToS m C)).map
        (Opposite.op (truncationStageHom m φ n))
        (truncationValue m φ (n + 1)) =
      truncationValue m φ n := by
  rfl

/-- The transition morphism of truncation objects in the characteristic
groupoid. -/
def truncationStep (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    truncationObject m φ n ⟶ truncationObject m φ (n + 1) :=
  Quiver.Hom.op <|
    CategoryOfElements.homMk (truncationElement m φ (n + 1))
      (truncationElement m φ n) (Opposite.op (truncationStageHom m φ n))
      (truncationValue_natural m φ n)

/-- Truncation objects of the characteristic groupoid lie over the corresponding
complete-local truncations. -/
theorem truncationObject_over (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (groupoids m C).p.obj (truncationObject m φ n) =
      (completeLocalSAlgebra m).stageOver n := by
  change Over.mk (truncationToCoproduct m φ n ≫ coproductToS m C) =
    Over.mk ((completeLocalSAlgebra m).truncationToS n)
  rw [truncationToCoproduct_comp_coproductToS]

/-- Truncation steps of the characteristic groupoid lift the truncation
thickenings in `Over Spec(Λ)`. -/
theorem truncationStep_over (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (groupoids m C).p.IsHomLift ((completeLocalSAlgebra m).stageHom n)
      (truncationStep m φ n) := by
  apply IsHomLift.of_fac (groupoids m C).p _ _
    (truncationObject_over m φ n) (truncationObject_over m φ (n + 1))
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.eqToHom_left]
  change (completeLocalSAlgebra m).truncationMap n =
    𝟙 _ ≫ (completeLocalSAlgebra m).truncationMap n ≫ 𝟙 _
  simp

/-- The canonical formal object of `groupoids m C` over `Λ_m^∧`, with truncation
objects given by the `Spec(C)` summand factorization. -/
def formalObject (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) :
    FormalObject (groupoids m C) :=
  FormalObject.of (completeLocalSAlgebra m) (truncationObject m φ)
    (truncationStep m φ) (truncationObject_over m φ) (truncationStep_over m φ)

/-- The complete local algebra of `formalObject m φ` is `Λ_m^∧`. -/
theorem formalObject_base (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) :
    (formalObject m φ).base = completeLocalSAlgebra m := by
  rfl

/-- Stagewise, `formalObject m φ` lies over the truncations of `Λ_m^∧` with
transition maps lifting the truncation thickenings. -/
theorem formalObject_spec (m : MaximalSpectrum Λ)
    (φ : C →ₐ[Λ] CompletedLocalRing m.toPrimeSpectrum) (n : ℕ) :
    (groupoids m C).p.obj ((formalObject m φ).objects n) =
        (formalObject m φ).base.stageOver n ∧
      (groupoids m C).p.IsHomLift ((formalObject m φ).base.stageHom n)
        ((formalObject m φ).step n) := by
  exact FormalObject.spec (formalObject m φ) n

end AlgebraicGeometry.GroupoidsOver.ApproximateVersalNecessity
