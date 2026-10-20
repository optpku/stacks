/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S X : Scheme.{u}} [IsNoetherian S]
variable (f : X ⟶ S) [FiniteType f]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
variable (HS : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
variable [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
variable (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
variable (ωS : RingedSpace.ModuleDerived S.toRingedSpace) (hωS : ωS.IsDualizingComplex HS)
variable (cover : FiniteSeparatedOpenCover f) (duality : ExceptionalInverseImageSetup f cover)

/- Definition 48.20.5: the complex obtained by the finite-cover construction is the dualizing
complex on `X` normalized relative to `ωS`. -/
@[stacks 0AUA] #check
  (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplexOnCover.complex :
    NormalizedDualizingComplexOnCover f HS HX ωS hωS cover duality →
      RingedSpace.ModuleDerived X.toRingedSpace)

end AlgebraicGeometry.Scheme.Hom
