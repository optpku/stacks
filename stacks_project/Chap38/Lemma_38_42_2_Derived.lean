/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Derived

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

universe u

/- This compatibility bridge re-exports derived eta for effective Cartier ideal sheaves. -/
#check (AlgebraicGeometry.Scheme.IdealSheafData.Eta.Derived.affineComparison_isomorphic :
  ∀ (A : CommRingCat.{u})
    (D : (Spec A).IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (f : nonZeroDivisors A)
    (_ : D = Scheme.idealSheafDataOfIdealOnSpec (Ideal.span {(f : A)})),
    IsIsomorphic
      (AlgebraicGeometry.Scheme.IdealSheafData.Eta.Derived.functor D ⋙
        Scheme.DerivedQCoh.affineGlobalSections A)
      (Scheme.DerivedQCoh.affineGlobalSections A ⋙
        CochainComplex.BerthelotOgus.Int.Derived.functor f))
