/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap75.Remark_75_20_6_Counit

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Hom
open CategoryTheory.Limits CategoryTheory.MonoidalClosed

universe u

/- Remark 75.20.6: for the affine Tor-independent base-change square of
Lemma 75.20.5, the internal-Hom base-change map commutes with multiplication and the map
induced by the counit `L(g')^* R(g')_* L ⟶ L`. -/
@[stacks 0E4T] #check
  (AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.InternalHom.map_counit_commSq :
    ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B) {X X' : AlgebraicSpace (Spec A)}
      (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk (Spec.map φ)))
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec A))))
      [IsQuasiCompact X] [IsQuasiSeparated X]
      [IsQuasiCompact X'] [IsQuasiSeparated X']
      [QuasiCompact f] [QuasiSeparated f]
      [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
      [MonoidalCategory (ModuleDerived X')] [BraidedCategory (ModuleDerived X')]
      [(modulePullbackDerived g').Monoidal]
      [IsIso (modulePullbackDerived.compComparison f' (specMap φ))]
      [IsIso (modulePullbackDerived.compComparison g' f)]
      (sq : IsPullback g' f' f (specMap φ)),
      TorIndependentOver (Over.mk f) (Over.mk (specMap φ)) →
        ∀ (H_X : MonoidalClosed (ModuleDerived X))
          (H_X' : MonoidalClosed (ModuleDerived X'))
          (M : ModuleDerived X) (L : ModuleDerived X'),
          CommSq
            (DerivedBaseChange.InternalHom.map sq.toCommSq H_X H_X' M
              ((Modules.pushforwardDerived g').obj L))
            (DerivedBaseChange.InternalHom.multiplication g' sq.toCommSq H_X H_X' M L)
            (DerivedBaseChange.InternalHom.adjunctionCounitMap g' f' H_X' M L)
            (𝟙 _))

section Multiplication

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)
variable (K' : ModuleDerived (ofOver (Over.mk (Spec.map φ))))

#check
  ((modulePullbackDerivedPushforwardAdjunction (specMap φ)).counit.app K' :
    (modulePullbackDerived (specMap φ)).obj
        ((Modules.pushforwardDerived (specMap φ)).obj K') ⟶ K')

end Multiplication
