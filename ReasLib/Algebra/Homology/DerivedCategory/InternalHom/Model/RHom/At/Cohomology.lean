/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.At
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Bifunctor.At
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Cohomology.Over
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Carrier-polymorphic cohomology of canonical `RHom`

This leaf specializes the generic K-injective cohomology owner to `ModuleCat.{v,r} R` while
keeping the carrier universe explicit.  It is the root module-category owner; the shorter
`RHom.Cohomology` facade is its standard same-universe specialization.

@stack 0E1U
-/

@[expose] public section

noncomputable section

universe r v g

open CategoryTheory
open CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.At.Cohomology

variable {R : Type r} [CommRing R]

/-- 0E1U: The degree-`n` cohomology functor of carrier-polymorphic canonical `RHom`. -/
@[stacks 0E1U "carrier-polymorphic canonical RHom cohomology"]
noncomputable abbrev functor (n : ℤ) [At.Has.{r, v} (R := R)] :
    (At.Derived.{r, v} (R := R))ᵒᵖ × At.Derived.{r, v} (R := R) ⥤
      ModuleCat.{v, r} R :=
  CochainComplex.Enriched.Over.RHom.Cohomology.functor
    (R := R) (C := ModuleCat.{v, r} R) n

/-- 0E1U: The universe-lifted shifted-Hom target for carrier-polymorphic canonical `RHom`. -/
@[stacks 0E1U "carrier-polymorphic shifted-Hom target"]
noncomputable abbrev shiftedFunctor (n : ℤ) :
    (At.Derived.{r, v} (R := R))ᵒᵖ × At.Derived.{r, v} (R := R) ⥤
      ModuleCat.{max (v + 1) r, r} R :=
  CochainComplex.Enriched.Over.RHom.Cohomology.shiftedFunctor
    (R := R) (C := ModuleCat.{v, r} R) n

/-- 0E1U: The universe-lifted cohomology functor of carrier-polymorphic canonical `RHom`. -/
@[stacks 0E1U "carrier-polymorphic lifted canonical RHom cohomology"]
noncomputable abbrev uliftFunctor (n : ℤ) [At.Has.{r, v} (R := R)] :
    (At.Derived.{r, v} (R := R))ᵒᵖ × At.Derived.{r, v} (R := R) ⥤
      ModuleCat.{max (v + 1) r, r} R :=
  CochainComplex.Enriched.Over.RHom.Cohomology.uliftFunctor
    (R := R) (C := ModuleCat.{v, r} R) n

section Grothendieck

variable [At.Has.{r, v} (R := R)]
variable [IsGrothendieckAbelian.{g} (ModuleCat.{v, r} R)]

/-- 0E1U: Lifted carrier-polymorphic canonical `RHom` cohomology is naturally shifted Hom. -/
@[stacks 0E1U "carrier-polymorphic canonical RHom cohomology comparison"]
noncomputable abbrev iso (n : ℤ) :
    uliftFunctor (R := R) n ≅ shiftedFunctor (R := R) n :=
  CochainComplex.Enriched.Over.RHom.Cohomology.iso
    (R := R) (C := ModuleCat.{v, r} R) n

/-- 0E1U: Carrier-polymorphic canonical `RHom` cohomology is linearly equivalent to shifted Hom. -/
@[stacks 0E1U "carrier-polymorphic canonical RHom cohomology linear equivalence"]
noncomputable abbrev linearEquiv
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ) :
    (functor (R := R) n).obj (Opposite.op K, L) ≃ₗ[R] ShiftedHom K L n :=
  CochainComplex.Enriched.Over.RHom.Cohomology.linearEquiv
    (R := R) (C := ModuleCat.{v, r} R) K L n

/-- 0E1U: Pointwise evaluation of the carrier-polymorphic cohomology equivalence. -/
@[simp, stacks 0E1U "carrier-polymorphic canonical RHom cohomology evaluation"]
theorem linearEquiv_apply
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ)
    (x : (functor (R := R) n).obj (Opposite.op K, L)) :
    linearEquiv (R := R) K L n x =
      ((iso (R := R) n).hom.app (Opposite.op K, L) (ULift.up x)).down :=
  CochainComplex.Enriched.Over.RHom.Cohomology.linearEquiv_apply
    (R := R) (C := ModuleCat.{v, r} R) K L n x

/-- 0E1U: Naturality of the carrier-polymorphic cohomology comparison in both variables. -/
@[reassoc, stacks 0E1U "carrier-polymorphic canonical RHom cohomology naturality"]
theorem iso_naturality (n : ℤ)
    {X Y : (At.Derived.{r, v} (R := R))ᵒᵖ × At.Derived.{r, v} (R := R)}
    (f : X ⟶ Y) :
    (uliftFunctor (R := R) n).map f ≫ (iso (R := R) n).hom.app Y =
      (iso (R := R) n).hom.app X ≫ (shiftedFunctor (R := R) n).map f :=
  CochainComplex.Enriched.Over.RHom.Cohomology.iso_naturality
    (R := R) (C := ModuleCat.{v, r} R) n f

/-- Naturality of the inverse carrier-polymorphic canonical cohomology comparison. -/
@[reassoc, stacks 0E1U "inverse carrier-polymorphic canonical RHom cohomology naturality"]
theorem iso_inv_naturality (n : ℤ)
    {X Y : (At.Derived.{r, v} (R := R))ᵒᵖ × At.Derived.{r, v} (R := R)}
    (f : X ⟶ Y) :
    (shiftedFunctor (R := R) n).map f ≫ (iso (R := R) n).inv.app Y =
      (iso (R := R) n).inv.app X ≫ (uliftFunctor (R := R) n).map f :=
  (iso (R := R) n).inv.naturality f

/-- The canonical cohomology comparison is natural in the contravariant source variable. -/
@[reassoc, stacks 0E1U "canonical RHom cohomology source naturality"]
theorem iso_natural_source
    {K₁ K₂ L : At.Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁) (n : ℤ) :
    (uliftFunctor (R := R) n).map (f.op, 𝟙 L) ≫
        (iso (R := R) n).hom.app (Opposite.op K₂, L) =
      (iso (R := R) n).hom.app (Opposite.op K₁, L) ≫
        (shiftedFunctor (R := R) n).map (f.op, 𝟙 L) :=
  iso_naturality (R := R) n
    ((f.op, 𝟙 L) : (Opposite.op K₁, L) ⟶ (Opposite.op K₂, L))

/-- The canonical cohomology comparison is natural in the covariant target variable. -/
@[reassoc, stacks 0E1U "canonical RHom cohomology target naturality"]
theorem iso_natural_target
    (K : At.Derived.{r, v} (R := R)) {L₁ L₂ : At.Derived.{r, v} (R := R)}
    (f : L₁ ⟶ L₂) (n : ℤ) :
    (uliftFunctor (R := R) n).map (𝟙 (Opposite.op K), f) ≫
        (iso (R := R) n).hom.app (Opposite.op K, L₂) =
      (iso (R := R) n).hom.app (Opposite.op K, L₁) ≫
        (shiftedFunctor (R := R) n).map (𝟙 (Opposite.op K), f) :=
  iso_naturality (R := R) n
    ((𝟙 (Opposite.op K), f) : (Opposite.op K, L₁) ⟶ (Opposite.op K, L₂))

/-- The inverse canonical cohomology comparison is natural in the contravariant source
variable. -/
@[reassoc, stacks 0E1U "inverse canonical RHom cohomology source naturality"]
theorem iso_inv_natural_source
    {K₁ K₂ L : At.Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁) (n : ℤ) :
    (shiftedFunctor (R := R) n).map (f.op, 𝟙 L) ≫
        (iso (R := R) n).inv.app (Opposite.op K₂, L) =
      (iso (R := R) n).inv.app (Opposite.op K₁, L) ≫
        (uliftFunctor (R := R) n).map (f.op, 𝟙 L) :=
  iso_inv_naturality (R := R) n
    ((f.op, 𝟙 L) : (Opposite.op K₁, L) ⟶ (Opposite.op K₂, L))

/-- The inverse canonical cohomology comparison is natural in the covariant target variable. -/
@[reassoc, stacks 0E1U "inverse canonical RHom cohomology target naturality"]
theorem iso_inv_natural_target
    (K : At.Derived.{r, v} (R := R)) {L₁ L₂ : At.Derived.{r, v} (R := R)}
    (f : L₁ ⟶ L₂) (n : ℤ) :
    (shiftedFunctor (R := R) n).map (𝟙 (Opposite.op K), f) ≫
        (iso (R := R) n).inv.app (Opposite.op K, L₂) =
      (iso (R := R) n).inv.app (Opposite.op K, L₁) ≫
        (uliftFunctor (R := R) n).map (𝟙 (Opposite.op K), f) :=
  iso_inv_naturality (R := R) n
    ((𝟙 (Opposite.op K), f) : (Opposite.op K, L₁) ⟶ (Opposite.op K, L₂))

/-- The canonical cohomology equivalence carries source maps to precomposition in shifted Hom. -/
@[simp, stacks 0E1U "canonical RHom cohomology source map"]
theorem linearEquiv_natural_source
    {K₁ K₂ L : At.Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁) (n : ℤ)
    (x : (functor (R := R) n).obj (Opposite.op K₁, L)) :
    linearEquiv (R := R) K₂ L n
        (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
          (At.map (R := R) f (𝟙 L))).hom x) =
      f ≫ linearEquiv (R := R) K₁ L n x := by
  rw [linearEquiv_apply, linearEquiv_apply]
  have h := ConcreteCategory.congr_hom
    (iso_natural_source (R := R) f n) (ULift.up x)
  simp only [ModuleCat.comp_apply] at h
  simp only [uliftFunctor, functor, shiftedFunctor, Functor.comp_map,
    ModuleCat.uliftFunctor_map, Functor.uncurry_obj_map, Functor.map_id,
    Category.comp_id, CategoryTheory.ShiftedHom.linearCoyoneda_map] at h
  change
    (iso (R := R) n).hom.app (Opposite.op K₂, L)
        (ULift.up (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
          (At.map (R := R) f (𝟙 L))).hom x)) =
      ULift.up (f ≫
        ((iso (R := R) n).hom.app (Opposite.op K₁, L) (ULift.up x)).down) at h
  exact congrArg ULift.down h

/-- The canonical cohomology equivalence carries target maps to postcomposition in shifted Hom. -/
@[simp, stacks 0E1U "canonical RHom cohomology target map"]
theorem linearEquiv_natural_target
    (K : At.Derived.{r, v} (R := R)) {L₁ L₂ : At.Derived.{r, v} (R := R)}
    (f : L₁ ⟶ L₂) (n : ℤ)
    (x : (functor (R := R) n).obj (Opposite.op K, L₁)) :
    linearEquiv (R := R) K L₂ n
        (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
          (At.map (R := R) (𝟙 K) f)).hom x) =
      linearEquiv (R := R) K L₁ n x ≫
        (shiftFunctor (At.Derived.{r, v} (R := R)) n).map f := by
  rw [linearEquiv_apply, linearEquiv_apply]
  have h := ConcreteCategory.congr_hom
    (iso_natural_target (R := R) K f n) (ULift.up x)
  simp only [ModuleCat.comp_apply] at h
  simp only [uliftFunctor, functor, shiftedFunctor, Functor.comp_map,
    ModuleCat.uliftFunctor_map, Functor.uncurry_obj_map, Functor.map_id] at h
  change
    (iso (R := R) n).hom.app (Opposite.op K, L₂)
        (ULift.up (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
          (At.map (R := R) (𝟙 K) f)).hom x)) =
      ULift.up
        (((iso (R := R) n).hom.app (Opposite.op K, L₁) (ULift.up x)).down ≫
          (shiftFunctor (At.Derived.{r, v} (R := R)) n).map f) at h
  exact congrArg ULift.down h

/-- 0E1U: The canonical carrier-polymorphic cohomology comparison from shifted derived morphisms
to canonical `RHom` cohomology. -/
@[stacks 0E1U "canonical RHom cohomology comparison"]
noncomputable def comparison
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ) :
    ShiftedHom K L n →ₗ[R] (functor (R := R) n).obj (Opposite.op K, L) :=
  (linearEquiv (R := R) K L n).symm.toLinearMap

/-- Evaluation of the canonical carrier-polymorphic cohomology comparison. -/
@[simp, stacks 0E1U "canonical RHom cohomology comparison evaluation"]
theorem comparison_apply
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ) (x : ShiftedHom K L n) :
    comparison (R := R) K L n x = (linearEquiv (R := R) K L n).symm x := rfl

/-- Applying the canonical cohomology equivalence after its comparison map recovers the shifted
morphism. -/
@[simp, stacks 0E1U "canonical RHom cohomology comparison left inverse"]
theorem linearEquiv_comparison
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ) (x : ShiftedHom K L n) :
    linearEquiv (R := R) K L n (comparison (R := R) K L n x) = x := by
  exact (linearEquiv (R := R) K L n).apply_symm_apply x

/-- Applying the canonical comparison after the cohomology equivalence recovers the cohomology
class. -/
@[simp, stacks 0E1U "canonical RHom cohomology comparison right inverse"]
theorem comparison_linearEquiv
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ)
    (x : (functor (R := R) n).obj (Opposite.op K, L)) :
    comparison (R := R) K L n (linearEquiv (R := R) K L n x) = x := by
  exact (linearEquiv (R := R) K L n).symm_apply_apply x

/-- The canonical comparison carries source composition to the cohomology map induced by
canonical `RHom` precomposition. -/
@[simp, stacks 0E1U "canonical RHom cohomology comparison source naturality"]
theorem comparison_natural_source
    {K₁ K₂ L : At.Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁) (n : ℤ)
    (x : ShiftedHom K₁ L n) :
    comparison (R := R) K₂ L n (f ≫ x) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
        (At.map (R := R) f (𝟙 L))).hom
          (comparison (R := R) K₁ L n x) := by
  apply (linearEquiv (R := R) K₂ L n).injective
  rw [linearEquiv_comparison, linearEquiv_natural_source, linearEquiv_comparison]

/-- The canonical comparison carries target composition to the cohomology map induced by the
canonical `RHom` target map. -/
@[simp, stacks 0E1U "canonical RHom cohomology comparison target naturality"]
theorem comparison_natural_target
    (K : At.Derived.{r, v} (R := R)) {L₁ L₂ : At.Derived.{r, v} (R := R)}
    (f : L₁ ⟶ L₂) (n : ℤ) (x : ShiftedHom K L₁ n) :
    comparison (R := R) K L₂ n
        (x ≫ (shiftFunctor (At.Derived.{r, v} (R := R)) n).map f) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
        (At.map (R := R) (𝟙 K) f)).hom
          (comparison (R := R) K L₁ n x) := by
  apply (linearEquiv (R := R) K L₂ n).injective
  rw [linearEquiv_comparison, linearEquiv_natural_target, linearEquiv_comparison]

/-- 0E1U: Degree-zero carrier-polymorphic canonical `RHom` cohomology is ordinary derived Hom. -/
@[stacks 0E1U "carrier-polymorphic degree-zero canonical RHom cohomology"]
noncomputable def linearEquiv_zero
    (K L : At.Derived.{r, v} (R := R)) :
    (functor (R := R) (0 : ℤ)).obj (Opposite.op K, L) ≃ₗ[R] (K ⟶ L) :=
  (linearEquiv (R := R) K L (0 : ℤ)).trans
    (ShiftedHom.zeroLinearEquiv R K L)

/-- 0E1U: Evaluation of the carrier-polymorphic degree-zero cohomology equivalence. -/
@[simp, stacks 0E1U "carrier-polymorphic degree-zero canonical RHom cohomology evaluation"]
theorem linearEquiv_zero_apply
    (K L : At.Derived.{r, v} (R := R))
    (x : (functor (R := R) (0 : ℤ)).obj (Opposite.op K, L)) :
    linearEquiv_zero (R := R) K L x =
      ShiftedHom.zeroLinearEquiv R K L
        (linearEquiv (R := R) K L (0 : ℤ) x) := rfl

/-- 0E1U: The degree-zero canonical cohomology comparison from derived morphisms to `RHom`
cohomology. -/
@[stacks 0E1U "canonical RHom degree-zero cohomology comparison"]
noncomputable def comparisonZero
    (K L : At.Derived.{r, v} (R := R)) :
    (K ⟶ L) →ₗ[R] (functor (R := R) (0 : ℤ)).obj (Opposite.op K, L) :=
  (linearEquiv_zero (R := R) K L).symm.toLinearMap

/-- Evaluation of the degree-zero canonical cohomology comparison. -/
@[simp, stacks 0E1U "canonical RHom degree-zero cohomology comparison evaluation"]
theorem comparisonZero_apply
    (K L : At.Derived.{r, v} (R := R)) (f : K ⟶ L) :
    comparisonZero (R := R) K L f = (linearEquiv_zero (R := R) K L).symm f := rfl

/-- Applying the degree-zero canonical cohomology equivalence after its comparison recovers the
derived morphism. -/
@[simp, stacks 0E1U "canonical RHom degree-zero comparison left inverse"]
theorem linearEquiv_zero_comparisonZero
    (K L : At.Derived.{r, v} (R := R)) (f : K ⟶ L) :
    linearEquiv_zero (R := R) K L (comparisonZero (R := R) K L f) = f := by
  exact (linearEquiv_zero (R := R) K L).apply_symm_apply f

/-- Applying the degree-zero comparison after the canonical cohomology equivalence recovers the
cohomology class. -/
@[simp, stacks 0E1U "canonical RHom degree-zero comparison right inverse"]
theorem comparisonZero_linearEquiv_zero
    (K L : At.Derived.{r, v} (R := R))
    (x : (functor (R := R) (0 : ℤ)).obj (Opposite.op K, L)) :
    comparisonZero (R := R) K L (linearEquiv_zero (R := R) K L x) = x := by
  exact (linearEquiv_zero (R := R) K L).symm_apply_apply x

/-- The degree-zero canonical cohomology equivalence carries source precomposition to ordinary
source composition. -/
@[simp, stacks 0E1U "canonical RHom degree-zero source naturality"]
theorem linearEquiv_zero_natural_source
    {K₁ K₂ L : At.Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁)
    (x : (functor (R := R) (0 : ℤ)).obj (Opposite.op K₁, L)) :
    linearEquiv_zero (R := R) K₂ L
        (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
          (At.map (R := R) f (𝟙 L))).hom x) =
      f ≫ linearEquiv_zero (R := R) K₁ L x := by
  rw [linearEquiv_zero_apply, linearEquiv_zero_apply,
    linearEquiv_natural_source]
  simp [ShiftedHom.zeroLinearEquiv, ShiftedHom.homEquiv, Category.assoc]

/-- The degree-zero canonical cohomology equivalence carries target maps to ordinary target
composition. -/
@[simp, stacks 0E1U "canonical RHom degree-zero target naturality"]
theorem linearEquiv_zero_natural_target
    (K : At.Derived.{r, v} (R := R))
    {L₁ L₂ : At.Derived.{r, v} (R := R)} (f : L₁ ⟶ L₂)
    (x : (functor (R := R) (0 : ℤ)).obj (Opposite.op K, L₁)) :
    linearEquiv_zero (R := R) K L₂
        (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
          (At.map (R := R) (𝟙 K) f)).hom x) =
      linearEquiv_zero (R := R) K L₁ x ≫ f := by
  rw [linearEquiv_zero_apply, linearEquiv_zero_apply,
    linearEquiv_natural_target]
  generalize linearEquiv (R := R) K L₁ 0 x = g
  change
    (g ≫ (shiftFunctor (At.Derived.{r, v} (R := R)) 0).map f) ≫
        (shiftFunctorZero' (At.Derived.{r, v} (R := R)) 0 rfl).hom.app L₂ =
      (g ≫ (shiftFunctorZero' (At.Derived.{r, v} (R := R)) 0 rfl).hom.app L₁) ≫ f
  rw [Category.assoc,
    (shiftFunctorZero' (At.Derived.{r, v} (R := R)) 0 rfl).hom.naturality f,
    ← Category.assoc]
  rw [Functor.id_map]
  rfl

/-- The degree-zero comparison carries source composition to the canonical `RHom` cohomology map. -/
@[simp, stacks 0E1U "canonical RHom degree-zero comparison source naturality"]
theorem comparisonZero_natural_source
    {K₁ K₂ L : At.Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁) (g' : K₁ ⟶ L) :
    comparisonZero (R := R) K₂ L (f ≫ g') =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
        (At.map (R := R) f (𝟙 L))).hom
          (comparisonZero (R := R) K₁ L g') := by
  apply (linearEquiv_zero (R := R) K₂ L).injective
  rw [linearEquiv_zero_comparisonZero, linearEquiv_zero_natural_source,
    linearEquiv_zero_comparisonZero]

/-- The degree-zero comparison carries target composition to the canonical `RHom` cohomology map. -/
@[simp, stacks 0E1U "canonical RHom degree-zero comparison target naturality"]
theorem comparisonZero_natural_target
    (K : At.Derived.{r, v} (R := R))
    {L₁ L₂ : At.Derived.{r, v} (R := R)} (f : L₁ ⟶ L₂) (g' : K ⟶ L₁) :
    comparisonZero (R := R) K L₂ (g' ≫ f) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
        (At.map (R := R) (𝟙 K) f)).hom
          (comparisonZero (R := R) K L₁ g') := by
  apply (linearEquiv_zero (R := R) K L₂).injective
  rw [linearEquiv_zero_comparisonZero, linearEquiv_zero_natural_target,
    linearEquiv_zero_comparisonZero]

end Grothendieck

end CategoryTheory.DerivedCategory.InternalHom.RHom.At.Cohomology

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.At.BifunctorComparison.Cohomology

variable {R : Type r} [CommRing R]
variable [At.Has.{r, v} (R := R)]
variable [MonoidalCategory (At.Derived.{r, v} (R := R))]
variable [IsGrothendieckAbelian.{g} (ModuleCat.{v, r} R)]

/-- 0E1U: The universe-lifted cohomology bifunctor of a selected internal Hom equipped with a
coherent carrier-polymorphic canonical-`RHom` comparison. -/
@[stacks 0E1U "coherent selected internal-Hom cohomology bifunctor"]
noncomputable abbrev functor
    (M : At.BifunctorComparison (R := R)) (n : ℤ) :
    (At.Derived.{r, v} (R := R))ᵒᵖ × At.Derived.{r, v} (R := R) ⥤
      ModuleCat.{max (v + 1) r, r} R :=
  Functor.PullbackInternalHom.Bifunctor.internalHomFunctor M.closed ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n ⋙
      ModuleCat.uliftFunctor.{max (v + 1) r, v} R

/-- The coherent selected cohomology comparison is the canonical comparison transported across
the supplied bifunctor isomorphism. -/
noncomputable def iso
    (M : At.BifunctorComparison (R := R)) (n : ℤ) :
    functor M n ≅ At.Cohomology.shiftedFunctor (R := R) n :=
  Functor.isoWhiskerRight M.functorIso.symm
      (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n ⋙
        ModuleCat.uliftFunctor.{max (v + 1) r, v} R) ≪≫
    At.Cohomology.iso (R := R) n

/-- The forward component of the coherent selected cohomology comparison. -/
@[simp, stacks 0E1U "coherent selected cohomology comparison component"]
theorem iso_hom_app
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ) :
    (iso M n).hom.app (Opposite.op K, L) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n ⋙
        ModuleCat.uliftFunctor.{max (v + 1) r, v} R).map
          (M.objIso K L).inv) ≫
        (At.Cohomology.iso (R := R) n).hom.app (Opposite.op K, L) := rfl

/-- The inverse component of the coherent selected cohomology comparison. -/
@[simp, stacks 0E1U "inverse coherent selected cohomology component"]
theorem iso_inv_app
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ) :
    (iso M n).inv.app (Opposite.op K, L) =
      (At.Cohomology.iso (R := R) n).inv.app (Opposite.op K, L) ≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n ⋙
          ModuleCat.uliftFunctor.{max (v + 1) r, v} R).map
            (M.objIso K L).hom) := rfl

/-- Naturality of the coherent selected cohomology comparison in both variables. -/
@[reassoc, stacks 0E1U "coherent selected cohomology naturality"]
theorem iso_naturality
    (M : At.BifunctorComparison (R := R)) (n : ℤ)
    {X Y : (At.Derived.{r, v} (R := R))ᵒᵖ × At.Derived.{r, v} (R := R)}
    (f : X ⟶ Y) :
    (functor M n).map f ≫ (iso M n).hom.app Y =
      (iso M n).hom.app X ≫ (At.Cohomology.shiftedFunctor (R := R) n).map f :=
  (iso M n).hom.naturality f

/-- Naturality of the inverse coherent selected cohomology comparison in both variables. -/
@[reassoc, stacks 0E1U "inverse coherent selected cohomology naturality"]
theorem iso_inv_naturality
    (M : At.BifunctorComparison (R := R)) (n : ℤ)
    {X Y : (At.Derived.{r, v} (R := R))ᵒᵖ × At.Derived.{r, v} (R := R)}
    (f : X ⟶ Y) :
    (At.Cohomology.shiftedFunctor (R := R) n).map f ≫ (iso M n).inv.app Y =
      (iso M n).inv.app X ≫ (functor M n).map f :=
  (iso M n).inv.naturality f

/-- The coherent selected cohomology comparison is natural in the contravariant source
variable. -/
@[reassoc, stacks 0E1U "coherent selected cohomology source naturality"]
theorem iso_natural_source
    (M : At.BifunctorComparison (R := R)) (n : ℤ)
    {K₁ K₂ L : At.Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁) :
    (functor M n).map (f.op, 𝟙 L) ≫
        (iso M n).hom.app (Opposite.op K₂, L) =
      (iso M n).hom.app (Opposite.op K₁, L) ≫
        (At.Cohomology.shiftedFunctor (R := R) n).map (f.op, 𝟙 L) :=
  iso_naturality M n
    ((f.op, 𝟙 L) : (Opposite.op K₁, L) ⟶ (Opposite.op K₂, L))

/-- The coherent selected cohomology comparison is natural in the covariant target
variable. -/
@[reassoc, stacks 0E1U "coherent selected cohomology target naturality"]
theorem iso_natural_target
    (M : At.BifunctorComparison (R := R)) (n : ℤ)
    (K : At.Derived.{r, v} (R := R))
    {L₁ L₂ : At.Derived.{r, v} (R := R)} (f : L₁ ⟶ L₂) :
    (functor M n).map (𝟙 (Opposite.op K), f) ≫
        (iso M n).hom.app (Opposite.op K, L₂) =
      (iso M n).hom.app (Opposite.op K, L₁) ≫
        (At.Cohomology.shiftedFunctor (R := R) n).map (𝟙 (Opposite.op K), f) :=
  iso_naturality M n
    ((𝟙 (Opposite.op K), f) : (Opposite.op K, L₁) ⟶ (Opposite.op K, L₂))

/-- The inverse coherent selected cohomology comparison is natural in the contravariant
source variable. -/
@[reassoc, stacks 0E1U "inverse coherent selected cohomology source naturality"]
theorem iso_inv_natural_source
    (M : At.BifunctorComparison (R := R)) (n : ℤ)
    {K₁ K₂ L : At.Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁) :
    (At.Cohomology.shiftedFunctor (R := R) n).map (f.op, 𝟙 L) ≫
        (iso M n).inv.app (Opposite.op K₂, L) =
      (iso M n).inv.app (Opposite.op K₁, L) ≫
        (functor M n).map (f.op, 𝟙 L) :=
  iso_inv_naturality M n
    ((f.op, 𝟙 L) : (Opposite.op K₁, L) ⟶ (Opposite.op K₂, L))

/-- The inverse coherent selected cohomology comparison is natural in the covariant
target variable. -/
@[reassoc, stacks 0E1U "inverse coherent selected cohomology target naturality"]
theorem iso_inv_natural_target
    (M : At.BifunctorComparison (R := R)) (n : ℤ)
    (K : At.Derived.{r, v} (R := R))
    {L₁ L₂ : At.Derived.{r, v} (R := R)} (f : L₁ ⟶ L₂) :
    (At.Cohomology.shiftedFunctor (R := R) n).map (𝟙 (Opposite.op K), f) ≫
        (iso M n).inv.app (Opposite.op K, L₂) =
      (iso M n).inv.app (Opposite.op K, L₁) ≫
        (functor M n).map (𝟙 (Opposite.op K), f) :=
  iso_inv_naturality M n
    ((𝟙 (Opposite.op K), f) : (Opposite.op K, L₁) ⟶ (Opposite.op K, L₂))

/-- The coherent selected cohomology equivalence obtained from the selected internal Hom. -/
noncomputable def linearEquiv
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).obj
        ((MonoidalClosed.ihomOf M.closed K).obj L) ≃ₗ[R]
      ShiftedHom K L n :=
  (ULift.moduleEquiv (R := R)
      (M := (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).obj
        ((MonoidalClosed.ihomOf M.closed K).obj L))).symm.trans <|
    ((iso M n).app (Opposite.op K, L)).toLinearEquiv.trans <|
      ULift.moduleEquiv (R := R) (M := ShiftedHom K L n)

/-- Evaluation of the coherent selected cohomology equivalence. -/
@[simp, stacks 0E1U "coherent selected cohomology equivalence evaluation"]
theorem linearEquiv_apply
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).obj
      ((MonoidalClosed.ihomOf M.closed K).obj L)) :
    linearEquiv M K L n x =
      ((iso M n).hom.app (Opposite.op K, L) (ULift.up x)).down := rfl

/-- The coherent selected cohomology equivalence after transport to canonical `RHom`. -/
@[simp, stacks 0E1U "coherent selected cohomology canonical transport"]
theorem linearEquiv_eq_canonical
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).obj
      ((MonoidalClosed.ihomOf M.closed K).obj L)) :
    linearEquiv M K L n x =
      At.Cohomology.linearEquiv (R := R) K L n
        (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
          (M.objIso K L).inv).hom x) := by
  rw [linearEquiv_apply, At.Cohomology.linearEquiv_apply, iso_hom_app]
  simp only [Functor.comp_map, ModuleCat.uliftFunctor_map]
  rfl

/-- The coherent selected cohomology equivalence carries source precomposition to shifted Hom. -/
@[simp, stacks 0E1U "coherent selected cohomology source naturality"]
theorem linearEquiv_natural_source
    (M : At.BifunctorComparison (R := R))
    {K₁ K₂ L : At.Derived.{r, v} (R := R)}
    (f : K₂ ⟶ K₁) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).obj
      ((MonoidalClosed.ihomOf M.closed K₁).obj L)) :
    linearEquiv M K₂ L n
        (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
          ((MonoidalClosed.preOf M.closed f).app L)).hom x) =
      f ≫ linearEquiv M K₁ L n x := by
  rw [linearEquiv_apply, linearEquiv_apply]
  have h := ConcreteCategory.congr_hom
    (iso_natural_source M n f) (ULift.up x)
  simp only [ModuleCat.comp_apply] at h
  simp only [functor, At.Cohomology.shiftedFunctor, Functor.comp_map,
    ModuleCat.uliftFunctor_map, Functor.uncurry_obj_map, Functor.map_id,
    Category.comp_id, CategoryTheory.ShiftedHom.linearCoyoneda_map] at h
  change
    (iso M n).hom.app (Opposite.op K₂, L)
        (ULift.up (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
          ((MonoidalClosed.preOf M.closed f).app L)).hom x)) =
      ULift.up (f ≫
        ((iso M n).hom.app (Opposite.op K₁, L) (ULift.up x)).down) at h
  exact congrArg ULift.down h

/-- The coherent selected cohomology equivalence carries target maps to shifted Hom. -/
@[simp, stacks 0E1U "coherent selected cohomology target naturality"]
theorem linearEquiv_natural_target
    (M : At.BifunctorComparison (R := R))
    (K : At.Derived.{r, v} (R := R))
    {L₁ L₂ : At.Derived.{r, v} (R := R)}
    (f : L₁ ⟶ L₂) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).obj
      ((MonoidalClosed.ihomOf M.closed K).obj L₁)) :
    linearEquiv M K L₂ n
        (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
          ((MonoidalClosed.ihomOf M.closed K).map f)).hom x) =
      linearEquiv M K L₁ n x ≫
        (shiftFunctor (At.Derived.{r, v} (R := R)) n).map f := by
  rw [linearEquiv_apply, linearEquiv_apply]
  have h := ConcreteCategory.congr_hom
    (iso_natural_target M n K f) (ULift.up x)
  simp only [ModuleCat.comp_apply] at h
  simp only [functor, At.Cohomology.shiftedFunctor, Functor.comp_map,
    ModuleCat.uliftFunctor_map, Functor.uncurry_obj_map, Functor.map_id,
    CategoryTheory.unop_id, NatTrans.id_app, Category.id_comp,
    CategoryTheory.ShiftedHom.linearCoyoneda_map,
    CategoryTheory.ShiftedHom.targetMap_id] at h
  change
    (iso M n).hom.app (Opposite.op K, L₂)
        (ULift.up (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
          ((MonoidalClosed.ihomOf M.closed K).map f)).hom x)) =
      ULift.up
        (((iso M n).hom.app (Opposite.op K, L₁) (ULift.up x)).down ≫
          (shiftFunctor (At.Derived.{r, v} (R := R)) n).map f) at h
  exact congrArg ULift.down h

/-- The inverse coherent selected cohomology comparison from shifted Hom to cohomology. -/
noncomputable def comparison
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ) :
    ShiftedHom K L n →ₗ[R]
      (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).obj
        ((MonoidalClosed.ihomOf M.closed K).obj L) :=
  (linearEquiv M K L n).symm.toLinearMap

/-- Evaluation of the inverse coherent selected cohomology comparison. -/
@[simp, stacks 0E1U "coherent selected cohomology comparison evaluation"]
theorem comparison_apply
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ) (x : ShiftedHom K L n) :
    comparison M K L n x = (linearEquiv M K L n).symm x := rfl

/-- The inverse coherent comparison after transport to canonical `RHom`. -/
@[simp, stacks 0E1U "coherent selected cohomology canonical comparison"]
theorem comparison_eq_canonical
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ) (x : ShiftedHom K L n) :
    comparison M K L n x =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
        (M.objIso K L).hom).hom
          (At.Cohomology.comparison (R := R) K L n x) := by
  apply (linearEquiv M K L n).injective
  rw [comparison_apply, (linearEquiv M K L n).apply_symm_apply,
    linearEquiv_eq_canonical]
  let z := At.Cohomology.comparison (R := R) K L n x
  have hz :
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
        (M.objIso K L).inv).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
            (M.objIso K L).hom).hom z) = z := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.hom_inv_id,
      Functor.map_id, ModuleCat.id_apply]
  rw [hz, At.Cohomology.linearEquiv_comparison]

/-- The selected cohomology equivalence is a left inverse to its comparison map. -/
@[simp]
theorem linearEquiv_comparison
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ) (x : ShiftedHom K L n) :
    linearEquiv M K L n (comparison M K L n x) = x := by
  exact (linearEquiv M K L n).apply_symm_apply x

/-- The selected comparison is a left inverse to its cohomology equivalence. -/
@[simp]
theorem comparison_linearEquiv
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (n : ℤ)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).obj
      ((MonoidalClosed.ihomOf M.closed K).obj L)) :
    comparison M K L n (linearEquiv M K L n x) = x := by
  exact (linearEquiv M K L n).symm_apply_apply x

/-- The selected comparison carries source composition to the induced cohomology map. -/
@[simp]
theorem comparison_natural_source
    (M : At.BifunctorComparison (R := R))
    {K₁ K₂ L : At.Derived.{r, v} (R := R)}
    (f : K₂ ⟶ K₁) (n : ℤ) (x : ShiftedHom K₁ L n) :
    comparison M K₂ L n (f ≫ x) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
        ((MonoidalClosed.preOf M.closed f).app L)).hom
          (comparison M K₁ L n x) := by
  apply (linearEquiv M K₂ L n).injective
  rw [linearEquiv_comparison, linearEquiv_natural_source, linearEquiv_comparison]

/-- The selected comparison carries target composition to the induced cohomology map. -/
@[simp]
theorem comparison_natural_target
    (M : At.BifunctorComparison (R := R))
    (K : At.Derived.{r, v} (R := R))
    {L₁ L₂ : At.Derived.{r, v} (R := R)}
    (f : L₁ ⟶ L₂) (n : ℤ) (x : ShiftedHom K L₁ n) :
    comparison M K L₂ n
        (x ≫ (shiftFunctor (At.Derived.{r, v} (R := R)) n).map f) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) n).map
        ((MonoidalClosed.ihomOf M.closed K).map f)).hom
          (comparison M K L₁ n x) := by
  apply (linearEquiv M K L₂ n).injective
  rw [linearEquiv_comparison, linearEquiv_natural_target, linearEquiv_comparison]

/-- The coherent selected degree-zero cohomology equivalence. -/
noncomputable def linearEquiv_zero
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).obj
        ((MonoidalClosed.ihomOf M.closed K).obj L) ≃ₗ[R] (K ⟶ L) :=
  (linearEquiv M K L (0 : ℤ)).trans (ShiftedHom.zeroLinearEquiv R K L)

/-- Evaluation of the coherent selected degree-zero cohomology equivalence. -/
@[simp, stacks 0E1U "coherent selected degree-zero cohomology evaluation"]
theorem linearEquiv_zero_apply
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).obj
      ((MonoidalClosed.ihomOf M.closed K).obj L)) :
    linearEquiv_zero M K L x =
      ShiftedHom.zeroLinearEquiv R K L (linearEquiv M K L (0 : ℤ) x) := rfl

/-- The degree-zero selected cohomology equivalence is the canonical one after object transport. -/
@[simp]
theorem linearEquiv_zero_eq_canonical
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).obj
      ((MonoidalClosed.ihomOf M.closed K).obj L)) :
    linearEquiv_zero M K L x =
      At.Cohomology.linearEquiv_zero (R := R) K L
        (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
          (M.objIso K L).inv).hom x) := by
  rw [linearEquiv_zero_apply, At.Cohomology.linearEquiv_zero_apply,
    linearEquiv_eq_canonical]

/-- The degree-zero selected cohomology equivalence carries source precomposition to composition. -/
@[simp]
theorem linearEquiv_zero_natural_source
    (M : At.BifunctorComparison (R := R))
    {K₁ K₂ L : At.Derived.{r, v} (R := R)}
    (f : K₂ ⟶ K₁)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).obj
      ((MonoidalClosed.ihomOf M.closed K₁).obj L)) :
    linearEquiv_zero M K₂ L
        (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
          ((MonoidalClosed.preOf M.closed f).app L)).hom x) =
      f ≫ linearEquiv_zero M K₁ L x := by
  rw [linearEquiv_zero_apply, linearEquiv_zero_apply,
    linearEquiv_natural_source]
  simp [ShiftedHom.zeroLinearEquiv, ShiftedHom.homEquiv, Category.assoc]

/-- The degree-zero selected cohomology equivalence carries target maps to composition. -/
@[simp]
theorem linearEquiv_zero_natural_target
    (M : At.BifunctorComparison (R := R))
    (K : At.Derived.{r, v} (R := R))
    {L₁ L₂ : At.Derived.{r, v} (R := R)}
    (f : L₁ ⟶ L₂)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).obj
      ((MonoidalClosed.ihomOf M.closed K).obj L₁)) :
    linearEquiv_zero M K L₂
        (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
          ((MonoidalClosed.ihomOf M.closed K).map f)).hom x) =
      linearEquiv_zero M K L₁ x ≫ f := by
  rw [linearEquiv_zero_apply, linearEquiv_zero_apply,
    linearEquiv_natural_target]
  generalize linearEquiv M K L₁ 0 x = g
  change
    (g ≫ (shiftFunctor (At.Derived.{r, v} (R := R)) 0).map f) ≫
        (shiftFunctorZero' (At.Derived.{r, v} (R := R)) 0 rfl).hom.app L₂ =
      (g ≫ (shiftFunctorZero' (At.Derived.{r, v} (R := R)) 0 rfl).hom.app L₁) ≫ f
  rw [Category.assoc,
    (shiftFunctorZero' (At.Derived.{r, v} (R := R)) 0 rfl).hom.naturality f,
    ← Category.assoc]
  rw [Functor.id_map]
  rfl

/-- The coherent selected degree-zero comparison from derived morphisms to cohomology. -/
noncomputable def comparisonZero
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) :
    (K ⟶ L) →ₗ[R]
      (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).obj
        ((MonoidalClosed.ihomOf M.closed K).obj L) :=
  (linearEquiv_zero M K L).symm.toLinearMap

/-- Evaluation of the coherent selected degree-zero comparison. -/
@[simp, stacks 0E1U "coherent selected degree-zero comparison evaluation"]
theorem comparisonZero_apply
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (f : K ⟶ L) :
    comparisonZero M K L f = (linearEquiv_zero M K L).symm f := rfl

/-- The degree-zero selected comparison is the canonical comparison after object transport. -/
@[simp]
theorem comparisonZero_eq_canonical
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (f : K ⟶ L) :
    comparisonZero M K L f =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
        (M.objIso K L).hom).hom
          (At.Cohomology.comparisonZero (R := R) K L f) := by
  apply (linearEquiv_zero M K L).injective
  rw [comparisonZero_apply, (linearEquiv_zero M K L).apply_symm_apply,
    linearEquiv_zero_eq_canonical]
  let z := At.Cohomology.comparisonZero (R := R) K L f
  have hz :
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
        (M.objIso K L).inv).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
            (M.objIso K L).hom).hom z) = z := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.hom_inv_id,
      Functor.map_id, ModuleCat.id_apply]
  rw [hz, At.Cohomology.linearEquiv_zero_comparisonZero]

/-- The degree-zero selected equivalence is a left inverse to its comparison map. -/
@[simp]
theorem linearEquiv_zero_comparisonZero
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R)) (f : K ⟶ L) :
    linearEquiv_zero M K L (comparisonZero M K L f) = f := by
  exact (linearEquiv_zero M K L).apply_symm_apply f

/-- The degree-zero selected comparison is a left inverse to its cohomology equivalence. -/
@[simp]
theorem comparisonZero_linearEquiv_zero
    (M : At.BifunctorComparison (R := R))
    (K L : At.Derived.{r, v} (R := R))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).obj
      ((MonoidalClosed.ihomOf M.closed K).obj L)) :
    comparisonZero M K L (linearEquiv_zero M K L x) = x := by
  exact (linearEquiv_zero M K L).symm_apply_apply x

/-- The degree-zero selected comparison carries source composition to the induced cohomology map. -/
@[simp]
theorem comparisonZero_natural_source
    (M : At.BifunctorComparison (R := R))
    {K₁ K₂ L : At.Derived.{r, v} (R := R)}
    (f : K₂ ⟶ K₁) (g' : K₁ ⟶ L) :
    comparisonZero M K₂ L (f ≫ g') =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
        ((MonoidalClosed.preOf M.closed f).app L)).hom
          (comparisonZero M K₁ L g') := by
  apply (linearEquiv_zero M K₂ L).injective
  rw [linearEquiv_zero_comparisonZero, linearEquiv_zero_natural_source,
    linearEquiv_zero_comparisonZero]

/-- The degree-zero selected comparison carries target composition to the induced cohomology map. -/
@[simp]
theorem comparisonZero_natural_target
    (M : At.BifunctorComparison (R := R))
    (K : At.Derived.{r, v} (R := R))
    {L₁ L₂ : At.Derived.{r, v} (R := R)}
    (f : L₁ ⟶ L₂) (g' : K ⟶ L₁) :
    comparisonZero M K L₂ (g' ≫ f) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{v, r} R) (0 : ℤ)).map
        ((MonoidalClosed.ihomOf M.closed K).map f)).hom
          (comparisonZero M K L₁ g') := by
  apply (linearEquiv_zero M K L₂).injective
  rw [linearEquiv_zero_comparisonZero, linearEquiv_zero_natural_target,
    linearEquiv_zero_comparisonZero]

end CategoryTheory.DerivedCategory.InternalHom.RHom.At.BifunctorComparison.Cohomology
