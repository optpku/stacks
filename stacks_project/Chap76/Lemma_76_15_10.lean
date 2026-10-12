/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_15_10_BaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {X Y Z W Z' W' : AlgebraicSpace S}
variable (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
variable (f : Z ⟶ W)
variable (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g)
variable [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
variable [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
variable [Flat g]

/- Lemma 76.15.10 (1): Let `S` be a scheme. In a fibre product diagram of algebraic
spaces over `S` with `h' : W ⟶ Y` formally unramified and `g : X ⟶ Y` flat, the
corresponding map `Z' ⟶ W'` of universal first-order thickenings is flat. -/
@[stacks 060C]
#check
  (IsUniversalFirstOrder.comparison_flat g iZ fZ iW fW f leftSq :
    Flat (IsUniversalFirstOrder.comparison iZ fZ iW fW f g ⟨leftSq.w⟩))

/- Lemma 76.15.10 (2): In this case the canonical map
`(Modules.pullback f).obj (Hom.conormalSheaf iW) ⟶ Hom.conormalSheaf iZ` is an
isomorphism. -/
@[stacks 060C]
#check
  (IsUniversalFirstOrder.conormalMap_isIso g iZ fZ iW fW f leftSq :
    IsIso (IsUniversalFirstOrder.conormalMap iZ fZ iW fW f g ⟨leftSq.w⟩))
