/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Definition_96_12_1_Restriction
public import stacks_project.Chap96.Definition_96_12_1_LocallyQuasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver

universe u

/- Definition 96.12.1: let `p : X ⟶ (Sch/S)_fppf` be a category fibred in
groupoids. Let `F` be a presheaf of `𝒪_X`-modules. We say `F` is locally
quasi-coherent if `F` is a sheaf for the étale topology and for every object
`x` of `X` the restriction `x* F|_{U_étale}` is a quasi-coherent sheaf.
Here `U = p(x)`. -/
@[stacks 06WJ] #check IsLocallyQuasicoherent
