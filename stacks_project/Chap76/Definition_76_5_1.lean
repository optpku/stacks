/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/- Definition 76.5.1: Let `i : Z ⟶ X` be an immersion of algebraic spaces. The
conormal sheaf `C_{Z/X}` of `Z` in `X`, or the conormal sheaf of `i`, is the
quasi-coherent `𝒪_Z`-module `I / I²` of the coborder closed immersion
`Z ⟶ X \ ∂Z`. -/
@[stacks 04CN]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.conormalSheaf i : Z.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.conormalSheaf_isQuasicoherent i :
  (AlgebraicGeometry.AlgebraicSpace.Hom.conormalSheaf i).IsQuasicoherent)
