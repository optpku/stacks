/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Bockstein
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reduction of the derived eta functor modulo an ideal

Modulo an invertible ideal, the derived eta construction is represented by the Bockstein
cohomology complex of the successive ideal-power quotients.  The statement is intrinsic to an
object of the derived category and uses the canonical eta and Bockstein owners.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Derived

variable {X : RingedSpace.{u}}

section

variable [∀ K L : CochainComplex X.Modules ℤ,
  HomologicalComplex.HasMapBifunctor K L (curriedTensor X.Modules) (up ℤ)]
variable [DerivedCategory.DerivedTensor.Has (C := X.Modules)]

/-- Lemma 20.55.8 (0GT9): for every derived module `M`, reduction of `Lη_I M` modulo `I`
is isomorphic to the derived image of the canonical Bockstein cohomology complex `H^•(M / I)`. -/
@[stacks 0GT9]
theorem tensorQuotient_isomorphic_bockstein
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (M : DerivedCategory X.Modules) :
    IsIsomorphic
      ((functor I).obj M ⊗ᴸ
        (DerivedCategory.singleFunctor X.Modules 0).obj (cokernel I.arrow))
      (DerivedCategory.Q.obj (Bockstein.complex I M)) := sorry

end

end AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Derived
