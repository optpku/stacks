module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.KInjective.Over
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.DerivedHom

/-!
# Integral compatibility facade for K-injective Hom comparisons

The generic owner is `CochainComplex.Enriched.Over.RHom`.  The integral linear-map declarations
retain the historical `ℤ` module structures; the underlying shifted morphism is delegated to the
generic comparison.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory
open DifferentialGradedCategory
open CategoryTheory.CochainComplex.Enriched.Over
open scoped DifferentialGradedCategory

namespace CategoryTheory.CochainComplex.Enriched

variable {C : Type u} [Category.{v} C]

/-- The historical integral K-injective function-level comparison. -/
@[stacks 0CS6 "K-injective enriched Hom cohomology as derived Hom"]
abbrev injectiveDerivedHomOfHomology [Abelian C] [HasDerivedCategory.{w} C]
    (K M I : CochainComplex C ℤ) (i : M ⟶ I)
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K I).homology n) :
    DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj M)⟦n⟧ :=
  Over.RHom.injectiveDerivedHomOfHomology (R := ℤ) K i n x

/-- The historical integral K-injective linear comparison. -/
@[stacks 0CS6 "K-injective Hom cohomology to derived Ext"]
noncomputable def injectiveDerivedHomLinearMap
    [Abelian C] [HasDerivedCategory.{w} C]
    (K M I : CochainComplex C ℤ) (i : M ⟶ I)
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ) :
    (DifferentialGradedCategory.homComplex K I).homology n →ₗ[ℤ]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) n where
  toFun := injectiveDerivedHomOfHomology K M I i n
  map_add' := sorry
  map_smul' := sorry

/-- Pointwise evaluation of the historical integral K-injective linear comparison. -/
@[simp]
theorem injectiveDerivedHomLinearMap_apply
    [Abelian C] [HasDerivedCategory.{w} C]
    (K M I : CochainComplex C ℤ) (i : M ⟶ I)
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K I).homology n) :
    injectiveDerivedHomLinearMap K M I i n x =
      injectiveDerivedHomOfHomology K M I i n x := sorry

/-- The historical integral K-injective function comparison is bijective. -/
theorem injectiveDerivedHomOfHomology_bijective
    [Abelian C] [HasDerivedCategory.{w} C]
    (K M I : CochainComplex C ℤ) (i : M ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ) :
    Function.Bijective (injectiveDerivedHomOfHomology K M I i n) := sorry

/-- The historical integral bundled comparison is bijective. -/
theorem injectiveDerivedHomLinearMap_bijective
    [Abelian C] [HasDerivedCategory.{w} C]
    (K M I : CochainComplex C ℤ) (i : M ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ) :
    Function.Bijective (injectiveDerivedHomLinearMap K M I i n) := sorry

/-- The historical integral K-injective linear equivalence. -/
noncomputable def injectiveDerivedHomLinearEquiv
    [Abelian C] [HasDerivedCategory.{w} C]
    (K M I : CochainComplex C ℤ) (i : M ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ) :
    (DifferentialGradedCategory.homComplex K I).homology n ≃ₗ[ℤ]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) n :=
  LinearEquiv.ofBijective (injectiveDerivedHomLinearMap K M I i n)
    (injectiveDerivedHomLinearMap_bijective K M I i n)

/-- Pointwise evaluation of the historical integral K-injective linear equivalence. -/
@[simp]
theorem injectiveDerivedHomLinearEquiv_apply
    [Abelian C] [HasDerivedCategory.{w} C]
    (K M I : CochainComplex C ℤ) (i : M ⟶ I) [I.IsKInjective]
    [IsIso (DerivedCategory.Q.map i)] (n : ℤ)
    (x : (DifferentialGradedCategory.homComplex K I).homology n) :
    injectiveDerivedHomLinearEquiv K M I i n x =
      injectiveDerivedHomLinearMap K M I i n x := sorry

end CategoryTheory.CochainComplex.Enriched
