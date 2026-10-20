/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic
import StacksCheckRecall

@[expose] public section

-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

/-!
# Lemma 20.46.9

The reusable owner is the ringed-site internal-Hom theorem.  This chapter entry is only the
opens-site bridge, so it does not import Chap21 or introduce a second representative statement.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (DerivedCategory (Modules X))]
variable [MonoidalClosed (DerivedCategory (Modules X))]

/- Lemma 20.46.9 (08DM): if `E` is strictly perfect, then the derived internal Hom from `E` to
`F` is represented by the canonical internal-Hom complex `(ihom E).obj F`. -/
@[stacks 08DM]
#check fun (E F : CochainComplex (Modules X) ℤ)
    (hE : RingedSite.CochainComplex.IsStrictlyPerfect
      (X := opensRingedSite X) E) ↦
  RingedSite.CochainComplex.InternalHom.represents_of_strictlyPerfect E F hE

/- The canonical source property and the two internal-Hom objects remain visible for downstream
users without exposing chapter-local notation. -/
#check @RingedSite.CochainComplex.InternalHom.represents_of_strictlyPerfect
#check @RingedSite.CochainComplex.IsStrictlyPerfect

end AlgebraicGeometry.RingedSpace
