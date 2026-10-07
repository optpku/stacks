module

public import stacks_project.Chap76.Lemma_76_14_5_Pullback
public import stacks_project.Chap76.Lemma_76_15_9_BaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {X Y Z W Z' W' : AlgebraicSpace S}
variable (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
variable (f : Z ⟶ W) (f' : Z' ⟶ W')
variable (closedSq : CommSq f iZ iW f')
variable (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g)
variable (rightSq : IsPullback f' fZ fW g)
variable [FormallyUnramified (iW ≫ fW)] [IsUniversalFirstOrder iW fW]

/- Lemma 76.15.9 (1): Let `S` be a scheme. In a fibre product diagram of algebraic
spaces over `S` with `h' : W ⟶ Y` formally unramified, the base change
`h : Z ⟶ X` is formally unramified. -/
@[stacks 060B]
#check
  (FormallyUnramified.instIsStableUnderBaseChange.of_isPullback leftSq
    inferInstance : FormallyUnramified (iZ ≫ fZ))

/- Lemma 76.15.9 (2): If `W ⊂ W'` is a universal first-order thickening of `W`
over `Y`, then `Z = X ×_Y W ⊂ X ×_Y W'` is a universal first-order thickening
of `Z` over `X`. -/
@[stacks 060B]
#check
  (IsUniversalFirstOrder.of_isPullback g iZ fZ iW fW f f' closedSq leftSq rightSq :
    IsUniversalFirstOrder iZ fZ)

variable [FormallyUnramified (iZ ≫ fZ)] [IsUniversalFirstOrder iZ fZ]
variable (thickeningSq : IsPullback f iZ iW f')

/- Lemma 76.15.9 (3): In particular the canonical map
`(Modules.pullback f).obj (Hom.conormalSheaf iW) ⟶ Hom.conormalSheaf iZ` of
Lemma 76.15.8 is surjective. -/
@[stacks 060B]
#check
  (IsUniversalFirstOrder.conormalMap_epi g iZ fZ iW fW f f' leftSq thickeningSq
    rightSq : Epi (IsUniversalFirstOrder.conormalMap iZ fZ iW fW f g ⟨leftSq.w⟩))
