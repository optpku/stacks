/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_15_8_Comparison
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}}
variable {X Y Z W Z' W' : AlgebraicSpace S}
variable (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
variable (f : Z ⟶ W) (g : X ⟶ Y)
variable [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
variable [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
variable (sq : CommSq f (iZ ≫ fZ) (iW ≫ fW) g)

/- Lemma 76.15.8 (1): Let `S` be a scheme. A commutative square of algebraic
spaces over `S` whose horizontal arrows `h : Z ⟶ X` and `h' : W ⟶ Y` are
formally unramified induces a canonical morphism of universal first-order
thickenings `(f, f') : (Z ⊂ Z') ⟶ (W ⊂ W')` over `Y`. -/
@[stacks 060A]
#check
  (IsUniversalFirstOrder.comparison iZ fZ iW fW f g sq : Z' ⟶ W')

/- Lemma 76.15.8 (2): In particular the morphism of thickenings induces a
morphism of conormal sheaves
`(Modules.pullback f).obj (Hom.conormalSheaf iW) ⟶ Hom.conormalSheaf iZ`. -/
@[stacks 060A]
#check
  (IsUniversalFirstOrder.conormalMap iZ fZ iW fW f g sq :
    (Modules.pullback f).obj (Hom.conormalSheaf iW) ⟶ Hom.conormalSheaf iZ)
