/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.Family.Zariski
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

variable {S : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S}
variable {𝒱 : SemiRepresentableFamily.Over.{w} S}

/- Lemma 35.35.10 (1): a same-target refinement whose fiber over every target member is a
Zariski covering induces an equivalence on categories of scheme descent data. -/
@[stacks 02VY] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.isEquivalenceOfZariskiFibers :
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map (𝟙 S)) 𝒰) 𝒱) →
    (∀ j : 𝒱.index,
      SemiRepresentableFamily.Over.IsCovering Scheme.zariskiPrecoverage (φ.fiber j)) →
    (Scheme.DescentData.Pullback.functorOfHom φ).IsEquivalence)

/- Lemma 35.35.10 (2): restriction from schemes over `S` to descent data for any Zariski
covering family of `S` is an equivalence. -/
@[stacks 02VY] #check
  (AlgebraicGeometry.Scheme.DescentData.isEquivalenceOfZariskiCover :
    SemiRepresentableFamily.Over.IsCovering Scheme.zariskiPrecoverage 𝒰 →
    (Scheme.overPseudofunctor.toDescentData
      (fun i : 𝒰.index ↦ (𝒰.obj i).hom)).IsEquivalence)

end AlgebraicGeometry
