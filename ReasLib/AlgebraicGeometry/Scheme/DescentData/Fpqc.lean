/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.Family.FullyFaithful

/-!
# Fpqc descent data for schemes

The canonical functor from schemes over a base scheme to descent data for an fpqc covering
family is fully faithful.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.DescentData

variable {S : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S}

/-- Restriction from schemes over a base scheme to descent data for an fpqc covering family
is fully faithful. -/
theorem fullyFaithfulOfFpqcCover (h𝒰 : Scheme.FpqcCovering 𝒰.obj) :
    Nonempty (Scheme.overPseudofunctor.toDescentData
      (fun i : 𝒰.index ↦ (𝒰.obj i).hom)).FullyFaithful := sorry

end AlgebraicGeometry.Scheme.DescentData
