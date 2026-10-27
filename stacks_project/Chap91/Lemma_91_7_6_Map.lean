/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Transitivity
public import stacks_project.Chap91.Lemma_91_7_1_Obstruction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Ext

/-!
# Functoriality of derived Ext¹ along ringed-space pullback and coefficient maps

The maps `L(g)^*` and `L(g)^* F[0] ⟶ G[0]` induced by `g : Y ⟶ X` and an
`𝒪_Y`-linear coefficient map `c` act on `Ext⁽1⁾(Q NL[f], Q(F[0]))`, while
precomposition along `L(g)^* NL[f] ⟶ NL[g ≫ f]` acts on
`Ext⁽1⁾(Q NL[g ≫ f], Q(G[0]))`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

#check (AlgebraicGeometry.RingedSpace.Thickening.extOne_map :
  ∀ {S X Y : RingedSpace.{u}} {f : X ⟶ S} {g : Y ⟶ X}
    {F : X.Modules} {G : Y.Modules},
    ((g^*).obj F ⟶ G) →
    Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
      (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj F)) →
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X).obj NL[f]),
      (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)))

#check (AlgebraicGeometry.RingedSpace.Thickening.extOne_comap :
  ∀ {S X Y : RingedSpace.{u}} {G : Y.Modules} (f : X ⟶ S) (g : Y ⟶ X),
    Ext⁽(1 : ℤ)⁾((moduleQ Y).obj NL[g ≫ f],
      (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)) →
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X).obj NL[f]),
      (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)))

end AlgebraicGeometry.RingedSpace.Thickening
