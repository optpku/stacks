/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap91.Lemma_91_7_4
public import stacks_project.Chap91.Lemma_91_7_6
public import stacks_project.Chap91.Remark_91_7_5
public import stacks_project.Chap91.Remark_91_7_7_InverseImage
public import stacks_project.Chap91.Remark_91_7_7_Pullback
public import stacks_project.Chap91.Remark_91_7_7_Pushout
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Functoriality of square-zero f⁻¹𝒪_S-algebra extensions by pushout and pullback

In the identity-base setting of Lemma 91.7.6, the pushout of
0 ⟶ F ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 along c : g^* F ⟶ G is a square-zero
g⁻¹ f⁻¹ 𝒪_S-algebra extension 𝒪'_1 of g⁻¹ 𝒪_X by G, and the pullback of
0 ⟶ G ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0 along g^♯ is an extension 𝒪'_2. An S-morphism
Y' ⟶ X' compatible with g and c exists iff 𝒪'_1 ≅ 𝒪'_2 as such extensions,
which are classified by the identified Ext¹ groups
Ext¹_{g⁻¹ 𝒪_X}(NL, G) = Ext¹_{𝒪_Y}(L(g)^* NL, G).
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Solution

variable {S X Y : RingedSpace.{u}}
variable {f : X ⟶ S} {g : Y ⟶ X}
variable {F : X.Modules} {G : Y.Modules}

/- Remark 91.7.7 (1) Using pushout along c : g^* F ⟶ G we construct an extension
0 ⟶ G ⟶ 𝒪'_1 ⟶ g⁻¹ 𝒪_X ⟶ 0 of square-zero g⁻¹ f⁻¹ 𝒪_S-algebras. -/
@[stacks 0GQ2] #check pushoutAlong

/- Remark 91.7.7 (2) Using pullback along g^♯ : g⁻¹ 𝒪_X ⟶ 𝒪_Y we construct an
extension 0 ⟶ G ⟶ 𝒪'_2 ⟶ g⁻¹ 𝒪_X ⟶ 0 of square-zero g⁻¹ f⁻¹ 𝒪_S-algebras. -/
@[stacks 0GQ2] #check pullbackAlong

/-- Remark 91.7.7 (3) There exists an S-morphism Y' ⟶ X' compatible with g and c
if and only if pushoutAlong g c SX is isomorphic to pullbackAlong g SY as
g⁻¹ f⁻¹ 𝒪_S-algebra extensions of g⁻¹ 𝒪_X by G. -/
@[stacks 0GQ2]
theorem exists_fittingMap_iff_isoClass (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Nonempty (FittingMap (RelativeDiagram.ofIdentityBase c SX SY)) ↔
      isoClassMk (pushoutAlong g c SX) = isoClassMk (pullbackAlong g SY) := sorry

/- Remark 91.7.7 (4) These extensions are classified by
Ext¹_{g⁻¹ 𝒪_X}(NL_{g⁻¹ 𝒪_X / g⁻¹ f⁻¹ 𝒪_S}, G) = Ext¹_{𝒪_Y}(L(g)^* NL[f], G),
via tensor-hom adjunction, Modules Lemma 17.31.3, and derived pullback. -/
@[stacks 0GQ2] #check extOne_inverseImageIso

/-- Remark 91.7.7 (5) Via the bijection of Lemma 91.7.4, pushoutAlong g c SX is the
image of the class of SX under Ext¹(Q NL[f], Q(F[0])) → Ext¹(L(g)^* NL[f], Q(G[0])). -/
@[stacks 0GQ2]
theorem pushoutAlong_extClass (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    extOne_inverseImageIso f g G
        ((extensionEquiv (inverseImageTo g ≫ f) (restrictToInverseImage g G)).symm
          (isoClassMk (pushoutAlong g c SX))) =
      extOne_map c ((extensionEquiv f F).symm (isoClassMk SX)) := sorry

/-- Remark 91.7.7 (6) Via the bijection of Lemma 91.7.4, pullbackAlong g SY is the
image of the class of SY under Ext¹(Q NL[g ≫ f], Q(G[0])) →
Ext¹(L(g)^* NL[f], Q(G[0])). -/
@[stacks 0GQ2]
theorem pullbackAlong_extClass
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    extOne_inverseImageIso f g G
        ((extensionEquiv (inverseImageTo g ≫ f) (restrictToInverseImage g G)).symm
          (isoClassMk (pullbackAlong g SY))) =
      extOne_comap f g ((extensionEquiv (g ≫ f) G).symm (isoClassMk SY)) := sorry

end Solution
end AlgebraicGeometry.RingedSpace.Thickening
