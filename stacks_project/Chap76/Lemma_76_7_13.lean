module

public import stacks_project.Chap76.Lemma_76_7_13_Product
import StacksCheckRecall

/-!
# Relative differentials of a fibre product of algebraic spaces

The maps of Lemma 76.7.6 from the pulled-back relative differentials of the factors of a
fibre product of algebraic spaces assemble to an isomorphism onto the relative differentials
of the fibre product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.Product

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)

/- Lemma 76.7.13: the two canonical projection comparisons identify the relative
differentials of a fibre product of algebraic spaces with the direct sum of the pulled-back
relative differentials of its factors. -/
@[stacks 05ZD] #check
  (comparison_isIso f g :
    IsIso
      (comparison f g :
        ((Modules.pullback (pullback.fst f g)).obj (relativeDifferentials f) ⊞
          (Modules.pullback (pullback.snd f g)).obj (relativeDifferentials g)) ⟶
            relativeDifferentials (pullback.snd f g ≫ g)))
