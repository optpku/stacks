/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.QuasiCompact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] (K : Precoverage C) (U : C)

/- Definition 7.17.1: let C be a site. An object U of C is quasi-compact if
given a covering 𝒰 = {Uᵢ ⟶ U}_{i ∈ I} in C there exists another covering
𝒱 = {Vⱼ ⟶ U}_{j ∈ J} and a morphism 𝒱 ⟶ 𝒰 of families of maps with fixed
target given by id : U ⟶ U, α : J → I, and Vⱼ ⟶ U_{α(j)} (see Definition
7.8.1) such that the image of α is a finite subset of I. This is owned by
Precoverage.QuasiCompactObject. -/
@[stacks 090H] #check (K.QuasiCompactObject U)

#check @Coverage.QuasiCompactObject
#check @Coverage.QuasiCompactObject.finiteImageRefinement
