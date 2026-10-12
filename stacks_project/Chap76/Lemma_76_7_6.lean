/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_7_6_Comparison
public import stacks_project.Chap76.Lemma_76_7_6_Differentials
import StacksCheckRecall

/-!
# Functoriality of the sheaf of differentials of a morphism of algebraic spaces

A commutative square of algebraic spaces over a scheme `S` induces a canonical comparison
morphism on relative differentials, uniquely characterized by its action on universal
differentials.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {X X' Y Y' : AlgebraicSpace S}
variable (f : X' ⟶ X) (g : Y' ⟶ Y) (h : X ⟶ Y) (h' : X' ⟶ Y')
variable (sq : f ≫ h = h' ≫ g)

/- Lemma 76.7.6: a commutative square of algebraic spaces over a scheme `S` determines a
unique pullback comparison `c_f : f^* Ω_{X/Y} ⟶ Ω_{X'/Y'}`, characterized by carrying
`f^* d_{X/Y}(t)` to `d_{X'/Y'}(f^* t)` on local sections of `𝒪_X`. -/
@[stacks 04CX] #check (existsUnique_comparison f g h h' sq :
  ∃! tau : (Modules.pullback f).obj (relativeDifferentials h) ⟶ relativeDifferentials h',
    IsComparison f h h' tau)

/- The reusable owner supplies the canonical comparison as concrete data. -/
@[stacks 04CX] #check (comparison f g h h' sq :
  (Modules.pullback f).obj (relativeDifferentials h) ⟶ relativeDifferentials h')

/- Its source-facing characterization is available independently of the chosen square proof. -/
#check (comparison_isComparison f g h h' sq :
  IsComparison f h h' (comparison f g h h' sq))

