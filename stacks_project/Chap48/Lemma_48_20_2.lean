/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.Uniqueness

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Hom

universe u

/- Lemma 48.20.2: a normalized dualizing complex on a finite separated open cover is unique up to
unique isomorphism compatible with the local normalizations. -/
@[stacks 0AU7] #check
  (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplexOnCover.existsUniqueIso :
    ∀ {S X : Scheme.{u}} [IsNoetherian S]
      (f : X ⟶ S) [FiniteType f]
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
      (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
      (cover : FiniteSeparatedOpenCover f) (duality : ExceptionalInverseImageSetup f cover)
      (K K' : NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality),
      ∃! e : K.complex ≅ K'.complex,
        AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplexOnCover.IsCompatibleIso K K' e)
