/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Presheaf.Basic
public import stacks_project.Chap94.Definition_94_12_1_Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids

universe u w

/- Definition 96.3.1: let `p : X ⟶ (Sch/S)_fppf` be a category fibred in
groupoids. A presheaf on `X` is a `Type`-valued presheaf on the underlying
category of `X`. A morphism of presheaves on `X` is a morphism of those
presheaves. We denote `PSh(X)` the functor category `Presheaf X.total`. -/
@[stacks 06TJ] #check (fun {S : Scheme.{u}} (X : GroupoidsOver S) ↦ Presheaf X.total)

variable {S : Scheme.{u}} (X : GroupoidsOver S) {F G : Presheaf X.total}

/- Morphisms of presheaves on `X` are morphisms in `Presheaf X.total`. -/
@[stacks 06TJ] #check (F ⟶ G)
