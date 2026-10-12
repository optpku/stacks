/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.DerivedHom.Over

/-!
# K-injective computation of explicit-base-ring derived Hom

This leaf turns the generic `R`-linear derived-Hom comparison into a resolution-level
equivalence.  The K-injective resolution object itself is owned by the cochain-complex
resolution modules; this file only owns the Hom computation.
-/

@[expose] public section

noncomputable section

universe r u v w

open CategoryTheory
open CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.CochainComplex.Enriched.Over.RHom

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- The shifted derived morphism represented by Hom cohomology into a chosen K-injective target
resolution. -/
@[stacks 0CS6 "K-injective explicit-base-ring Hom cohomology comparison"]
def injectiveDerivedHomOfHomology [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) {M I : CochainComplex C ℤ} (i : M ⟶ I)
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ)
    (x : (homComplex (R := R) K I).homology n) :
    DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj M)⟦n⟧ :=
  derivedHomOfHomology (R := R) K I n x ≫
    (shiftFunctor _ n).map (asIso (DerivedCategory.Q.map i)).inv

/-- The K-injective Hom-cohomology comparison, bundled as an `R`-linear map. -/
@[stacks 0CS6 "K-injective explicit-base-ring Hom cohomology linear map"]
noncomputable def injectiveDerivedHomLinearMap [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) {M I : CochainComplex C ℤ} (i : M ⟶ I)
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ) :
    (homComplex (R := R) K I).homology n →ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) n where
  toFun := injectiveDerivedHomOfHomology (R := R) K i n
  map_add' := sorry
  map_smul' := sorry

/-- The bundled K-injective comparison evaluates to the canonical pointwise map. -/
@[simp]
theorem injectiveDerivedHomLinearMap_apply [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) {M I : CochainComplex C ℤ} (i : M ⟶ I)
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ)
    (x : (homComplex (R := R) K I).homology n) :
    injectiveDerivedHomLinearMap (R := R) K i n x =
      injectiveDerivedHomOfHomology (R := R) K i n x := sorry

/-- Hom cohomology into a K-injective resolution is bijective onto shifted derived Hom. -/
@[stacks 0CS6 "K-injective explicit-base-ring Hom comparison bijectivity"]
theorem injectiveDerivedHomOfHomology_bijective [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) {M I : CochainComplex C ℤ} (i : M ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ) :
    Function.Bijective (injectiveDerivedHomOfHomology (R := R) K i n) := sorry

/-- The bundled `R`-linear comparison has the same bijectivity statement as its underlying
function. -/
@[stacks 0CS6 "K-injective explicit-base-ring Hom linear-map bijectivity"]
theorem injectiveDerivedHomLinearMap_bijective [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) {M I : CochainComplex C ℤ} (i : M ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ) :
    Function.Bijective (injectiveDerivedHomLinearMap (R := R) K i n) := sorry

/-- The K-injective Hom-cohomology comparison as a linear equivalence. -/
@[stacks 0CS6 "K-injective explicit-base-ring Hom cohomology linear equivalence"]
noncomputable def injectiveDerivedHomLinearEquiv [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) {M I : CochainComplex C ℤ} (i : M ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ) :
    (homComplex (R := R) K I).homology n ≃ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) n :=
  LinearEquiv.ofBijective (injectiveDerivedHomLinearMap (R := R) K i n)
    (injectiveDerivedHomLinearMap_bijective (R := R) K i n)

/-- A resolution carries the quasi-isomorphism fact as data; this companion keeps that
source-facing fact at the API boundary instead of asking callers to install the derived
isomorphism instance themselves. -/
@[stacks 070Y "K-injective Hom comparison from a quasi-isomorphism"]
noncomputable def injectiveDerivedHomLinearEquiv_of_quasiIso [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) {M I : CochainComplex C ℤ} (i : M ⟶ I) [I.IsKInjective]
    [QuasiIso i] (n : ℤ) :
    (homComplex (R := R) K I).homology n ≃ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) n :=
  injectiveDerivedHomLinearEquiv (R := R) K i n

/-- The K-injective comparison for the identity resolution map. -/
@[stacks 070Y "self K-injective Hom comparison"]
noncomputable def injectiveDerivedHomLinearEquiv_self [HasDerivedCategory.{w} C]
    (K I : CochainComplex C ℤ) [I.IsKInjective] (n : ℤ) :
    (homComplex (R := R) K I).homology n ≃ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I) n :=
  injectiveDerivedHomLinearEquiv (R := R) K (𝟙 I) n

/-- The forward map of the K-injective linear equivalence is the canonical comparison. -/
@[simp]
theorem injectiveDerivedHomLinearEquiv_apply [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) {M I : CochainComplex C ℤ} (i : M ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ)
    (x : (homComplex (R := R) K I).homology n) :
    injectiveDerivedHomLinearEquiv (R := R) K i n x =
      injectiveDerivedHomLinearMap (R := R) K i n x := sorry

end CategoryTheory.CochainComplex.Enriched.Over.RHom
