/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Eta.Derived

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

universe u

/- Lemma 38.42.2 (1): derived ideal-sheaf eta preserves complexes with quasicoherent
cohomology. -/
@[stacks 0GTV] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.Eta.Derived.mapsTo :
    ∀ {X : Scheme.{u}} (D : X.IdealSheafData)
      [IsEffectiveCartierDivisor D.subschemeι],
      DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).inverseImage
            (RingedSpace.IdealSheaf.Eta.Derived.functor D.toSubobject))

/- Lemma 38.42.2 (2): on `Spec A` with divisor `V(f)`, ideal-sheaf derived eta corresponds
to ring-level derived eta under affine derived global sections. -/
@[stacks 0GTV] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.Eta.Derived.affineComparison_isomorphic :
    ∀ (A : CommRingCat.{u})
      (D : (Spec A).IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
      (f : nonZeroDivisors A)
      (_ : D = Scheme.idealSheafDataOfIdealOnSpec (Ideal.span {(f : A)})),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.IdealSheafData.Eta.Derived.functor D ⋙
          Scheme.DerivedQCoh.affineGlobalSections A)
        (Scheme.DerivedQCoh.affineGlobalSections A ⋙
          CochainComplex.BerthelotOgus.Int.Derived.functor f))
