/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Existence

@[expose] public section

open CategoryTheory

universe u

/- Lemma 48.20.4: for a scheme `X` of finite type over `S`, every finite open cover of
`X` by schemes separated over `S` admits a dualizing complex normalized relative to `ωS`
and the chosen cover. -/
@[stacks 0AU9] #check
  (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplexOnCover.nonempty :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
      (f : X ⟶ S) [AlgebraicGeometry.Scheme.Hom.FiniteType f]
      [MonoidalCategory
        (AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace)]
      (HS : MonoidalClosed
        (AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace))
      [MonoidalCategory
        (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)]
      (HX : MonoidalClosed
        (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace))
      (ωS : AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace)
      (hωS : ωS.IsDualizingComplex HS)
      (cover : AlgebraicGeometry.Scheme.Hom.FiniteSeparatedOpenCover f)
      (duality : AlgebraicGeometry.Scheme.Hom.ExceptionalInverseImageSetup f cover),
      Nonempty
        (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplexOnCover
          f HS HX ωS hωS cover duality))
