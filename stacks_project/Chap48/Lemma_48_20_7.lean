/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.NormalizedDualizing.OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.20.7: if `j : X ⟶ Y` is an open immersion of schemes of finite type over
`S`, then dualizing complexes `ωX` and `ωY` normalized relative to the same dualizing
complex `ωS` are canonically isomorphic after restricting `ωY` to `X`. -/
@[stacks 0AUC] #check
  (AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo.isIsomorphic_pullback_of_isOpenImmersion :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
      {X Y : Scheme.FiniteTypeOver S} (j : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion j.hom.left],
      let X' : Scheme := X.obj.left
      let Y' : Scheme := Y.obj.left
      let j' : X' ⟶ Y' := j.hom.left
      ∀ [MonoidalCategory (AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace)]
        (HS : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace))
        [MonoidalCategory (AlgebraicGeometry.RingedSpace.ModuleDerived X'.toRingedSpace)]
        (HX : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived X'.toRingedSpace))
        [MonoidalCategory (AlgebraicGeometry.RingedSpace.ModuleDerived Y'.toRingedSpace)]
        (HY : MonoidalClosed (AlgebraicGeometry.RingedSpace.ModuleDerived Y'.toRingedSpace))
        (ωS : AlgebraicGeometry.RingedSpace.ModuleDerived S.toRingedSpace)
        (hωS : ωS.IsDualizingComplex HS)
        (ωX : AlgebraicGeometry.RingedSpace.ModuleDerived X'.toRingedSpace)
        (ωY : AlgebraicGeometry.RingedSpace.ModuleDerived Y'.toRingedSpace)
        (hX : @AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo
          _ _ _ X.obj.hom (Scheme.FiniteTypeOver.instFiniteType X) _ HS _ HX ωS hωS ωX)
        (hY : @AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex.RelativeTo
          _ _ _ Y.obj.hom (Scheme.FiniteTypeOver.instFiniteType Y) _ HS _ HY ωS hωS ωY),
        IsIsomorphic ωX
          ((AlgebraicGeometry.RingedSpace.modulePullbackDerived j'.toShHom).obj ωY))
