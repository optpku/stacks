/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.InternalHom.GlobalCounit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange.InternalHom.Counit

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Hom
open CategoryTheory.Limits CategoryTheory.MonoidalClosed
open CategoryTheory.DerivedCategory CategoryTheory.Functor

universe u

/- Remark 75.20.6: for the affine Tor-independent base-change square of
Lemma 75.20.5, scalar-valued global derived Hom base change commutes with multiplication and the map
induced by the counit `L(g')^* R(g')_* L ⟶ L`. -/
@[stacks 0E4T] #check (AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.GlobalHom.map_counit_commSq :
  ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {X X' : AlgebraicSpace (Spec A)} (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map φ)))
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec A))))
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [IsQuasiCompact X'] [IsQuasiSeparated X']
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f (Hom.specMap φ))
    (hTor : TorIndependentOver (Over.mk f) (Over.mk (Hom.specMap φ)))
    (M : ModuleDerived X) (L : ModuleDerived X'),
    CommSq
      (Hom.DerivedBaseChange.GlobalHom.map sq.toCommSq M
        ((Modules.moduleDerivedPushforward g').obj L))
      (Hom.DerivedBaseChange.GlobalHom.multiplication sq.toCommSq M L)
      (Hom.DerivedBaseChange.GlobalHom.adjunctionCounitMap g' f' M L)
      (𝟙 _))

section Multiplication

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)
variable (K' : DerivedCategory (ModuleCat.{u} B))

#check
  ((ModuleCat.derivedExtensionRestrictionAdjunction φ.hom).counit.app K' :
    (ModuleCat.derivedExtensionOfScalars φ.hom).obj
        ((ModuleCat.derivedRestrictionOfScalars φ.hom).obj K') ⟶ K')

end Multiplication
