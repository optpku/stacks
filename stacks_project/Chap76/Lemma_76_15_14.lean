/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_15_14_Comparison
public import stacks_project.Chap76.Lemma_76_15_14_Transitivity
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.Differentials.Transitivity

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {X Y Z ZX ZY : AlgebraicSpace S}
variable (iX : Z ⟶ ZX) (fX : ZX ⟶ X) (iY : Z ⟶ ZY) (fY : ZY ⟶ Y) (f : X ⟶ Y)
variable [IsUniversalFirstOrder iX fX] [IsUniversalFirstOrder iY fY]
variable [FormallyUnramified (iX ≫ fX)] [FormallyUnramified (iY ≫ fY)]
variable (sq : CommSq (𝟙 Z) (iX ≫ fX) (iY ≫ fY) f)

/- Lemma 76.15.14: Let `S` be a scheme. Let a commutative triangle of algebraic
spaces over `S` have formally unramified morphisms `i : Z ⟶ X` and `j : Z ⟶ Y`.
Then there is a canonical exact sequence
`C_{Z/Y} ⟶ C_{Z/X} ⟶ i^* Ω_{X/Y} ⟶ 0`
where the first arrow comes from Lemma 76.15.8 and the second from
Lemma 76.15.13. Here `i := iX ≫ fX` and `j := iY ≫ fY` are recovered from
chosen universal first-order thickenings.
`C_{Z/Y}` and `C_{Z/X}` are the coborder expansions `conormal iY` and
`conormal iX`, which are `Hom.conormalSheaf` when that owner is available.
`i^* Ω_{X/Y} := (Modules.pullback (iX ≫ fX)).obj (relativeDifferentials f)`.
The first arrow is identity-pullback transport of
`IsUniversalFirstOrder.conormalMap iX fX iY fY (𝟙 Z) f sq`.
The second arrow is `Differentials.conormalMap iX fX (iX ≫ fX) f rfl`. -/
@[stacks 06BE]
#check
  (exact_and_epi iX fX iY fY f sq :
    (complex iX fX iY fY f sq).Exact ∧ Epi (map iX fX iY fY f sq))
