/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Derived
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Functor

/-!
# Derived morphisms represented by explicit-base-ring Hom cohomology

This leaf records the canonical map from cohomology of the `R`-linear enriched Hom complex to
shifted morphisms in the derived category.  K-injective computation and simultaneous derived-Hom
models are separate consumers of this map.
-/

@[expose] public section

noncomputable section

universe r u v w

open CategoryTheory
open ComplexShape HomotopyCategory
open CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.CochainComplex.Enriched.Over.RHom

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- The shifted derived morphism represented by a class in an explicit-base-ring Hom complex. -/
@[stacks 09LZ "explicit-base-ring Hom cohomology class as shifted derived Hom"]
def derivedHomOfHomology [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ)
    (x : (homComplex (R := R) K L).homology n) :
    DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧ :=
  (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).shiftedHomMap
    ((DerivedCategory.quotientCompQhIso C).app K)
    ((DerivedCategory.quotientCompQhIso C).app L) n
    (homotopyHomOfHomology (R := R) K L n x)

/-- The explicit-base-ring Hom-cohomology-to-derived-Hom comparison as an `R`-linear map. -/
@[stacks 09LZ "explicit-base-ring Hom cohomology to shifted derived Hom"]
noncomputable def derivedHomLinearMap [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (homComplex (R := R) K L).homology n →ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) n where
  toFun := derivedHomOfHomology K L n
  map_add' := sorry
  map_smul' := sorry

/-- The additive form of the explicit-base-ring Hom-cohomology comparison. -/
@[stacks 09LZ "explicit-base-ring Hom cohomology additive comparison"]
noncomputable abbrev derivedHomAddMonoidHom [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (homComplex (R := R) K L).homology n →+
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) n :=
  (derivedHomLinearMap (R := R) K L n).toAddMonoidHom

/-- Evaluation of the additive comparison is the canonical shifted derived morphism. -/
@[simp]
theorem derivedHomAddMonoidHom_apply [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ)
    (x : (homComplex (R := R) K L).homology n) :
    derivedHomAddMonoidHom (R := R) K L n x =
      derivedHomOfHomology (R := R) K L n x := sorry

/-- The linear comparison evaluates to the canonical shifted derived morphism. -/
@[simp]
theorem derivedHomLinearMap_apply [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ)
    (x : (homComplex (R := R) K L).homology n) :
    derivedHomLinearMap (R := R) K L n x = derivedHomOfHomology (R := R) K L n x := sorry

/-- The explicit-base-ring Hom-cohomology comparison is contravariantly natural in the source. -/
@[stacks 09LZ "source naturality of explicit-base-ring derived Hom cohomology"]
theorem derivedHomOfHomology_naturality_source [HasDerivedCategory.{w} C]
    {K₁ K₂ L : CochainComplex C ℤ} (f : K₂ ⟶ K₁) (n : ℤ)
    (x : (homComplex (R := R) K₁ L).homology n) :
    derivedHomOfHomology (R := R) K₂ L n
        (HomologicalComplex.homologyMap (homComplexMap f (𝟙 L)) n x) =
      DerivedCategory.Q.map f ≫ derivedHomOfHomology (R := R) K₁ L n x := sorry

/-- The explicit-base-ring Hom-cohomology comparison is covariantly natural in the target. -/
@[stacks 09LZ "target naturality of explicit-base-ring derived Hom cohomology"]
theorem derivedHomOfHomology_naturality_target [HasDerivedCategory.{w} C]
    {K L₁ L₂ : CochainComplex C ℤ} (g : L₁ ⟶ L₂) (n : ℤ)
    (x : (homComplex (R := R) K L₁).homology n) :
    derivedHomOfHomology (R := R) K L₂ n
        (HomologicalComplex.homologyMap (homComplexMap (𝟙 K) g) n x) =
      derivedHomOfHomology (R := R) K L₁ n x ≫ (DerivedCategory.Q.map g)⟦n⟧' := sorry

/-- The explicit-base-ring Hom-cohomology comparison is natural in both complexes. -/
@[stacks 09LZ "two-variable naturality of explicit-base-ring derived Hom cohomology"]
theorem derivedHomOfHomology_naturality [HasDerivedCategory.{w} C]
    {K₁ K₂ L₁ L₂ : CochainComplex C ℤ} (f : K₂ ⟶ K₁) (g : L₁ ⟶ L₂)
    (n : ℤ) (x : (homComplex (R := R) K₁ L₁).homology n) :
    derivedHomOfHomology (R := R) K₂ L₂ n
        (HomologicalComplex.homologyMap (homComplexMap f g) n x) =
      DerivedCategory.Q.map f ≫ derivedHomOfHomology (R := R) K₁ L₁ n x ≫
        (DerivedCategory.Q.map g)⟦n⟧' := sorry

/-- Explicit-base-ring Hom cohomology computes one shifted derived Hom module in degree `n`. -/
@[stacks 09LZ "explicit-base-ring Hom computes Ext in one degree"]
def ComputesExtInDegree [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ) : Prop :=
  Function.Bijective (derivedHomLinearMap (R := R) K L n)

/-- Explicit-base-ring Hom cohomology computes all shifted derived Hom modules. -/
@[stacks 09LZ "explicit-base-ring Hom computes Ext"]
def ComputesExt [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) : Prop :=
  ∀ n : ℤ, ComputesExtInDegree (R := R) K L n

/-- The canonical `R`-linear map from endomorphism-complex cohomology to shifted self-morphisms. -/
@[stacks 09LZ "explicit-base-ring endomorphism cohomology to self-Ext"]
noncomputable abbrev selfExtLinearMap [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    (homComplex (R := R) K K).homology n →ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj K) n :=
  derivedHomLinearMap (R := R) K K n

/-- Explicit-base-ring endomorphism cohomology computes self-`Ext` in one degree. -/
@[stacks 09LZ "explicit-base-ring endomorphisms compute self-Ext in one degree"]
abbrev ComputesSelfExtInDegree [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) : Prop :=
  Function.Bijective (selfExtLinearMap (R := R) K n)

/-- Explicit-base-ring endomorphism cohomology computes all shifted self-`Ext` groups. -/
@[stacks 09LZ "explicit-base-ring endomorphisms compute self-Ext"]
def ComputesSelfExt [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) : Prop :=
  ∀ n : ℤ, ComputesSelfExtInDegree (R := R) K n

end CategoryTheory.CochainComplex.Enriched.Over.RHom
