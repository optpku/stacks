/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.DescentData.Fpqc

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme.DescentData

variable {S : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S}

/- Remark 35.35.12: morphisms of schemes satisfy fpqc descent. Fullness constructs a
global morphism from a compatible morphism after fpqc base change, and faithfulness gives
its uniqueness; a surjective flat morphism of affine schemes is the singleton-cover case. -/
@[stacks 040L]
#check
  (AlgebraicGeometry.Scheme.DescentData.fullyFaithfulOfFpqcCover :
    (h𝒰 : Scheme.FpqcCovering 𝒰.obj) →
    Nonempty (Scheme.overPseudofunctor.toDescentData
      (fun i : 𝒰.index ↦ (𝒰.obj i).hom)).FullyFaithful)

end AlgebraicGeometry.Scheme.DescentData
