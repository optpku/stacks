/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.CoverIndependence

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Hom

universe u

/- Lemma 48.20.3: if a dualizing complex on a scheme of finite type over `S` is normalized
relative to `ωS` on one finite open cover by schemes separated over `S`, then there is a dualizing
complex normalized relative to `ωS` on any other such cover, with the same underlying complex. -/
@[stacks 0AU8] #check
  (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplexOnCover.existsOnCoverWithSameComplex :
    ∀ {S X : Scheme.{u}} [IsNoetherian S]
      (f : X ⟶ S) [FiniteType f]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
      (coverU coverV : FiniteSeparatedOpenCover f)
      (dualityU : ExceptionalInverseImageSetup f coverU)
      (dualityV : ExceptionalInverseImageSetup f coverV)
      (K : NormalizedDualizingComplexOnCover f HS HX ωS hωS coverU dualityU),
      ∃ K' : NormalizedDualizingComplexOnCover f HS HX ωS hωS coverV dualityV,
        K'.complex = K.complex)
