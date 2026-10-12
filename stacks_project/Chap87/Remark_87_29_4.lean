/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_24_4_FiniteType
public import stacks_project.Chap87.Lemma_87_27_3_ClosedImmersion
public import stacks_project.Chap87.Lemma_87_27_5_McQuillan
public import stacks_project.Chap87.Lemma_87_29_3_InverseSystem
public import stacks_project.Chap87.Lemma_87_9_10_Map
public import stacks_project.Chap87.Remark_87_28_1_Universal_property_restricted_power_series_RestrictedPowerSeries

/-!
# Affine space over a McQuillan affine formal algebraic space

Let `A` be a weakly admissible topological ring and `X = Spf(A)`, a McQuillan
affine formal algebraic space. A morphism `Y ⟶ X` of affine formal algebraic
spaces need not have McQuillan source.

Closed immersions are McQuillan and correspond to taut continuous maps
`φ : A →+* B` with closed kernel and dense image (Lemma 87.27.5). Whether
`B` equals the weak-ideal completion of `A ⧸ K` as in Example 87.27.6, and
whether such maps are surjective and open, is left open.

Finite-type morphisms correspond to objects `(B_I)` of
`FiniteTypeInverseSystem` by Lemma 87.29.3, and those stages are generated
over `A ⧸ I` by a uniform number of elements; whether the inverse-limit
projections are surjective is left open.

If `Y` is also McQuillan then `φ` is taut and topologically of finite type
(Lemma 87.29.2), so the morphism factors as a closed immersion
`Y ⟶ affineSpace hA r ⟶ Spf(A)`. The questions above are deferred to the
countably indexed case.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- Restricted power series in finitely many variables over a weakly admissible
ring remain weakly admissible. -/
instance instIsWeaklyAdmissibleRing_restrictedPowerSeries
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {r : ℕ} :
    TopologicalRing.IsWeaklyAdmissibleRing (RestrictedPowerSeries (Fin r) A) :=
  sorry

/-- The coefficient algebra map into restricted power series is continuous. -/
theorem continuous_algebraMap_restrictedPowerSeries
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {r : ℕ} :
    Continuous (algebraMap A (RestrictedPowerSeries (Fin r) A)) :=
  sorry

/-- The structure morphism `Spec(RestrictedPowerSeries (Fin r) A) ⟶ S`. -/
def restrictedPowerSeriesSpecHom {S : Scheme.{u}} {A : Type u}
    [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ) :
    Spec (.of (RestrictedPowerSeries (Fin r) A)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap A (RestrictedPowerSeries (Fin r) A))) ≫ hA

/-- Unfolding of `restrictedPowerSeriesSpecHom` as the composite of `Spec.map`
of the coefficient algebra map with the structure morphism of `A`. -/
theorem restrictedPowerSeriesSpecHom_eq {S : Scheme.{u}} {A : Type u}
    [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ) :
    restrictedPowerSeriesSpecHom hA r =
      Spec.map (CommRingCat.ofHom (algebraMap A (RestrictedPowerSeries (Fin r) A))) ≫
        hA :=
  sorry

/-- Affine `r`-space over `Spf(A)`, as `Spf` of restricted power series
`RestrictedPowerSeries (Fin r) A`. -/
def affineSpace {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  spf (RestrictedPowerSeries (Fin r) A) (restrictedPowerSeriesSpecHom hA r)

/-- Unfolding of `affineSpace` as `Spf` of restricted power series. -/
theorem affineSpace_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    affineSpace hA r =
      spf (RestrictedPowerSeries (Fin r) A) (restrictedPowerSeriesSpecHom hA r) :=
  sorry

/-- The structure morphism `affineSpace hA r ⟶ Spf(A)` induced by the
coefficient algebra map. -/
def affineSpace.proj {S : Scheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    affineSpace hA r ⟶ spf A hA :=
  spfMap (algebraMap A (RestrictedPowerSeries (Fin r) A))
    continuous_algebraMap_restrictedPowerSeries
    (restrictedPowerSeriesSpecHom_eq hA r).symm

/-- Unfolding of `affineSpace.proj` as `spfMap` of the coefficient algebra
map. -/
theorem affineSpace.proj_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    affineSpace.proj hA r =
      spfMap (algebraMap A (RestrictedPowerSeries (Fin r) A))
        continuous_algebraMap_restrictedPowerSeries
        (restrictedPowerSeriesSpecHom_eq hA r).symm :=
  sorry

/-- Affine `r`-space over a McQuillan affine formal spectrum is McQuillan
affine. -/
instance instIsMcQuillanAffine_affineSpace {S : Scheme.{u}} {A : Type u}
    [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S) (r : ℕ)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    IsMcQuillanAffine (affineSpace hA r).obj :=
  sorry

/-- Remark 87.29.4 (1): Let `A` be a topological ring and let `(B_I)` be an
object of `FiniteTypeInverseSystem A`. By Lemma 87.29.3 this is the algebraic
counterpart of a finite-type morphism `Y ⟶ Spf(A)` with
`Y = colim Spec(B_I)`. There exists a fixed natural number `r` such that each
stage `B_I` is generated by `r` elements over `A ⧸ I`. -/
@[stacks 0AJK]
theorem exists_generatorCard_eq {A : Type u} [CommRing A] [TopologicalSpace A]
    (B : FiniteTypeInverseSystem A) :
    ∃ r : ℕ, ∀ I : (WeakIdealOfDefinition A)ᵒᵖ,
      ∃ f : MvPolynomial (Fin r) (A ⧸ I.unop.ideal) →ₐ[A ⧸ I.unop.ideal]
          B.obj.right.obj I,
        Function.Surjective f :=
  sorry

/-- Remark 87.29.4 (2): Let `A` be a weakly admissible topological ring, let
`X = Spf(A)` over a scheme `S`, and let `f : Y ⟶ X` be a finite-type morphism
of McQuillan affine formal algebraic spaces. Then `f` corresponds to a taut
continuous map that is topologically of finite type (Lemma 87.29.2), so `f`
factors as a closed immersion into `affineSpace hA r` followed by
`affineSpace.proj hA r`. -/
@[stacks 0AJK]
theorem exists_closedImmersion_affineSpace {S : Scheme.{u}} {A : Type u}
    [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A]
    (hA : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    {Y : (Over S)ᵒᵖ ⥤ Type u} [IsMcQuillanAffine Y]
    (f : Y ⟶ (spf A hA).obj) [FiniteType f] :
    ∃ r : ℕ, ∃ i : Y ⟶ (affineSpace hA r).obj,
      ClosedImmersion i ∧
        i ≫ (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
            (affineSpace.proj hA r) = f :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace

