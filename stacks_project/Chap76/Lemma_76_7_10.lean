/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Differentials
import StacksCheckRecall

/-!
# Conormal sequence of an immersion of algebraic spaces

An immersion of algebraic spaces over a base algebraic space has a canonical
right-exact sequence relating the conormal sheaf to relative differentials.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {B X Z : AlgebraicSpace S}
variable (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ B)

/- Lemma 76.7.10: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `i : Z ⟶ X` be an immersion of algebraic spaces over `B`. There is a
canonical exact sequence `C_{Z/X} ⟶ i^* Ω_{X/B} ⟶ Ω_{Z/B} ⟶ 0`, where the
first arrow is induced by `d_{X/B}` and the second arrow comes from
Lemma 76.7.6. -/
@[stacks 05ZA] #check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials.exact_and_epi i f :
  (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials.complex i f).Exact ∧
    Epi (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials.comparison i f))

/- The first arrow is the `d_{X/B}`-induced map out of the conormal sheaf. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials.map i f :
  Hom.conormalSheaf i ⟶ (Modules.pullback i).obj (relativeDifferentials f))

/- The second arrow is the Lemma 76.7.6 comparison on relative differentials. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Differentials.comparison i f :
  (Modules.pullback i).obj (relativeDifferentials f) ⟶ relativeDifferentials (i ≫ f))
