/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.DerivedHom.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex

/-!
# Integral compatibility facade for derived Hom comparisons

The canonical function-level and generic `R`-linear APIs live in
`CochainComplex.Enriched.Over.RHom`.  The integral linear-map declarations below retain the
historical `ℤ` module instance used by older clients.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open ComplexShape HomotopyCategory
open DifferentialGradedCategory
open CategoryTheory.CochainComplex.Enriched.Over
open scoped DifferentialGradedCategory

namespace CategoryTheory.CochainComplex.Enriched

variable {C : Type u} [Category.{v} C]

/-- The historical integral function-level derived Hom comparison. -/
@[stacks 09LZ "enriched Hom cohomology class as shifted derived Hom"]
abbrev derivedHomOfHomology [Abelian C] [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K L).homology n) :
    DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧ :=
  Over.RHom.derivedHomOfHomology (R := ℤ) K L n x

/-- The historical integral linear comparison, retaining the canonical `ℤ` module structures. -/
@[stacks 09LZ "enriched Hom cohomology to shifted derived Hom"]
noncomputable def derivedHomLinearMap [Abelian C] [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (DifferentialGradedCategory.homComplex K L).homology n →ₗ[ℤ]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) n where
  toFun := derivedHomOfHomology K L n
  map_add' := sorry
  map_smul' := sorry

/-- Pointwise evaluation of the historical integral linear comparison. -/
@[simp]
theorem derivedHomLinearMap_apply [Abelian C] [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K L).homology n) :
    derivedHomLinearMap K L n x = derivedHomOfHomology K L n x := sorry

/-- The historical integral additive comparison. -/
@[stacks 09LZ "enriched Hom cohomology additive comparison"]
noncomputable abbrev derivedHomAddMonoidHom [Abelian C] [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (DifferentialGradedCategory.homComplex K L).homology n →+
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) n :=
  (derivedHomLinearMap K L n).toAddMonoidHom

/-- Pointwise evaluation of the historical integral additive comparison. -/
@[simp]
theorem derivedHomAddMonoidHom_apply [Abelian C] [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K L).homology n) :
    derivedHomAddMonoidHom K L n x = derivedHomOfHomology K L n x := sorry

/-- Source naturality of the historical integral derived Hom comparison. -/
@[stacks 09LZ "source naturality of enriched Hom cohomology in the derived category"]
theorem derivedHomOfHomology_naturality_source
    [Abelian C] [HasDerivedCategory.{w} C]
    {K₁ K₂ L : CochainComplex C ℤ} (f : K₂ ⟶ K₁) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K₁ L).homology n) :
    derivedHomOfHomology K₂ L n
        (HomologicalComplex.homologyMap (homComplexMap f (𝟙 L)) n x) =
      DerivedCategory.Q.map f ≫ derivedHomOfHomology K₁ L n x := sorry

/-- Target naturality of the historical integral derived Hom comparison. -/
@[stacks 09LZ "target naturality of enriched Hom cohomology in the derived category"]
theorem derivedHomOfHomology_naturality_target
    [Abelian C] [HasDerivedCategory.{w} C]
    {K L₁ L₂ : CochainComplex C ℤ} (g : L₁ ⟶ L₂) (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K L₁).homology n) :
    derivedHomOfHomology K L₂ n
        (HomologicalComplex.homologyMap (homComplexMap (𝟙 K) g) n x) =
      derivedHomOfHomology K L₁ n x ≫ (DerivedCategory.Q.map g)⟦n⟧' := sorry

/-- Two-variable naturality of the historical integral derived Hom comparison. -/
theorem derivedHomOfHomology_naturality
    [Abelian C] [HasDerivedCategory.{w} C]
    {K₁ K₂ L₁ L₂ : CochainComplex C ℤ} (f : K₂ ⟶ K₁) (g : L₁ ⟶ L₂)
    (n : ℤ) (x : (DifferentialGradedCategory.homComplex K₁ L₁).homology n) :
    derivedHomOfHomology K₂ L₂ n
        (HomologicalComplex.homologyMap (homComplexMap f g) n x) =
      DerivedCategory.Q.map f ≫ derivedHomOfHomology K₁ L₁ n x ≫
        (DerivedCategory.Q.map g)⟦n⟧' := sorry

/-- The historical integral degreewise `Ext` computation predicate. -/
@[stacks 09LZ "enriched Hom computes Ext in one degree"]
def ComputesExtInDegree [Abelian C] [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) (n : ℤ) : Prop :=
  Function.Bijective (derivedHomLinearMap K L n)

/-- The historical integral all-degree `Ext` computation predicate. -/
@[stacks 09LZ "enriched Hom computes Ext"]
def ComputesExt [Abelian C] [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) : Prop :=
  ∀ n : ℤ, ComputesExtInDegree K L n

/-- The historical integral self-`Ext` linear map. -/
@[stacks 09LZ "enriched endomorphism cohomology to self-Ext"]
noncomputable abbrev selfExtLinearMap [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    (DifferentialGradedCategory.endomorphismDGA (R := ℤ) K).homology n →ₗ[ℤ]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj K) n :=
  derivedHomLinearMap K K n

/-- The historical integral degreewise self-`Ext` computation predicate. -/
@[stacks 09LZ "enriched endomorphisms compute self-Ext in one degree"]
abbrev ComputesSelfExtInDegree [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) : Prop :=
  Function.Bijective (selfExtLinearMap K n)

/-- The historical integral all-degree self-`Ext` computation predicate. -/
@[stacks 09LZ "enriched endomorphisms compute self-Ext"]
def ComputesSelfExt [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) : Prop :=
  ∀ n : ℤ, ComputesSelfExtInDegree K n

end CategoryTheory.CochainComplex.Enriched
