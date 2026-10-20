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

/-!
# Lemma 20.46.10

The K-flatness statement is owned by the reusable ringed-site internal-Hom API.  This chapter
entry is a thin source-label bridge and deliberately has no Chap21 dependency.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Lemma 20.46.10: if `F` is K-flat and `E` is strictly perfect, then the canonical internal-Hom
complex `(ihom E).obj F` is K-flat. -/
@[stacks 0GM5]
#check fun (E F : CochainComplex (Modules X) ℤ)
    (hE : RingedSite.CochainComplex.IsStrictlyPerfect
      (X := opensRingedSite X) E) (hF : F.IsKFlat) ↦
  RingedSite.CochainComplex.InternalHom.isKFlat_of_strictlyPerfect E F hE hF

#check @RingedSite.CochainComplex.InternalHom.isKFlat_of_strictlyPerfect
#check @RingedSite.CochainComplex.IsStrictlyPerfect
#check @CochainComplex.IsKFlat

end AlgebraicGeometry.RingedSpace
