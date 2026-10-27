/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.BaseChange

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

universe u

/- Remark 99.7.2: Under arbitrary base change, quasi-coherent quotients flat over the
 test scheme identify with the original quotients after composing the test scheme's
 structure morphism with the base-change map. -/
@[stacks 08IT] #check (AlgebraicGeometry.AlgebraicSpace.Quot.functorChangeBaseEquiv :
  ∀ {S : Scheme.{u}} {X B B' : AlgebraicSpace S}
    (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (σ : (SchemeOver B')ᵒᵖ),
    (AlgebraicGeometry.AlgebraicSpace.Quot.functor (pullback.snd f g)
      ((Modules.pullback (pullback.fst f g)).obj F)).obj σ ≃
      ((CostructuredArrow.map g).op ⋙
        AlgebraicGeometry.AlgebraicSpace.Quot.functor f F).obj σ)

/- Remark 99.7.2: The same base-change identification holds for finitely presented
 quasi-coherent quotients flat over the test scheme. -/
@[stacks 08IT] #check (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctorChangeBaseEquiv :
  ∀ {S : Scheme.{u}} {X B B' : AlgebraicSpace S}
    (f : X ⟶ B) (g : B' ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    (σ : (SchemeOver B')ᵒᵖ),
    (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor (pullback.snd f g)
      ((Modules.pullback (pullback.fst f g)).obj F)).obj σ ≃
      ((CostructuredArrow.map g).op ⋙
        AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor f F).obj σ)
