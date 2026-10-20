/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Existence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

noncomputable section

/- Definition 76.15.5 (1): Let `S` be a scheme. Let `h : Z ⟶ X` be a formally
unramified morphism of algebraic spaces over `S`. The universal first-order
thickening of `Z` over `X` is the thickening `Z ⊂ Z'` constructed in
Lemma 76.15.4. -/
@[stacks 0607]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.exists_of_formallyUnramified :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (h : Z ⟶ X) [FormallyUnramified h],
      ∃ (Z' : AlgebraicSpace S) (i : Z ⟶ Z') (f : Z' ⟶ X),
        i ≫ f = h ∧ IsUniversalFirstOrder i f)

variable {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S}
variable (i : Z ⟶ Z') (f : Z' ⟶ X) [IsUniversalFirstOrder i f]
variable [FormallyUnramified (i ≫ f)]

/- Definition 76.15.5 (2): The conormal sheaf of `Z` over `X`, often denoted
`C_{Z/X}`, is the conormal sheaf of `Z` in its universal first-order thickening
`Z'` over `X`. The formally unramified morphism under discussion is
`h = i ≫ f`. -/
@[stacks 0607]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.conormalSheaf i : Z.Modules)
