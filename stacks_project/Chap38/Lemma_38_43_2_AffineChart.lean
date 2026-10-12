/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry nonZeroDivisors

universe u

#check (AlgebraicGeometry.Scheme.DivisorComplexChart.of :
  {X : Scheme.{u}} → (D : X.IdealSheafData) →
    (M : RingedSpace.ModuleDerived X.toRingedSpace) →
    (U : X.affineOpens) → (generator : Γ(X, U)) →
    (model : CochainComplex (ModuleCat Γ(X, U)) ℤ) →
    CochainComplex.bounded (ModuleCat Γ(X, U)) model →
    model.IsTermwiseFiniteFree →
    generator ∈ nonZeroDivisors Γ(X, U) →
    D.ideal U = Ideal.span {generator} →
    IsIsomorphic (DerivedCategory.Q.obj model)
      ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj M) →
    AlgebraicGeometry.Scheme.DivisorComplexChart D M)

#check (AlgebraicGeometry.Scheme.DivisorComplexChart.spec :
  {X : Scheme.{u}} → {D : X.IdealSheafData} →
    {M : RingedSpace.ModuleDerived X.toRingedSpace} →
    (C : AlgebraicGeometry.Scheme.DivisorComplexChart D M) →
    CochainComplex.bounded (ModuleCat Γ(X, C.U)) C.model ∧
      C.model.IsTermwiseFiniteFree ∧
      C.generator ∈ nonZeroDivisors Γ(X, C.U) ∧
      D.ideal C.U = Ideal.span {C.generator} ∧
      IsIsomorphic (DerivedCategory.Q.obj C.model)
        ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace C.U).obj M))

#check (AlgebraicGeometry.Scheme.DivisorComplexChart.ideal :
  {X : Scheme.{u}} → {D : X.IdealSheafData} →
    {M : RingedSpace.ModuleDerived X.toRingedSpace} →
    (C : AlgebraicGeometry.Scheme.DivisorComplexChart D M) →
    ℤ → Ideal Γ(X, C.U))

#check (AlgebraicGeometry.Scheme.DivisorComplexChart.ideal_def :
  {X : Scheme.{u}} → {D : X.IdealSheafData} →
    {M : RingedSpace.ModuleDerived X.toRingedSpace} →
    (C : AlgebraicGeometry.Scheme.DivisorComplexChart D M) → (i : ℤ) →
    C.ideal i =
      @CochainComplex.BerthelotOgus.Int.etaDeterminantalIdeal
        _ _ C.generator C.model i (C.finiteFree.finite i)
          (C.finiteFree.free (i + 1)) (C.finiteFree.finite (i + 1)))

#check (AlgebraicGeometry.Scheme.IsGoodTriple :
  {X : Scheme.{u}} → X.IdealSheafData →
    RingedSpace.ModuleDerived X.toRingedSpace → Prop)

#check (AlgebraicGeometry.Scheme.isGoodTriple_iff :
  {X : Scheme.{u}} → (D : X.IdealSheafData) →
    (M : RingedSpace.ModuleDerived X.toRingedSpace) →
    AlgebraicGeometry.Scheme.IsGoodTriple D M ↔
      ∀ x : D.subscheme,
        ∃ C : AlgebraicGeometry.Scheme.DivisorComplexChart D M,
          D.subschemeι x ∈ (C.U : X.Opens) ∧
            ∀ i : ℤ, (C.ideal i).IsPrincipal)
