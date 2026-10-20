/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.«60_24_8_1»
public import stacks_project.Chap60.«60_24_8_1_Mate»
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open RingedSite
open RingedSite.Hom
open RingedSite.Hom.DerivedBaseChange

noncomputable section

universe u v w z

/-- Remark 60.24.8 (Base change map) (1): in the affine situation of Remark 60.24.1, with
`S = Spec A` and `S' = Spec A'`, if `F` is the pullback of an `O_{X'/S'}`-module `F'`, there is a
canonical sheaf-level base-change map
`L(S' ⟶ S)^* Rτ_{X'/S',*} F' ⟶ Rτ_{X/S,*} F`, where `τ_{X/S}` and `τ_{X'/S'}` are the crystalline
structure morphisms of Remark 60.9.6.  Here `f` and `f'` model those structure morphisms and `g`
models `S' ⟶ S`. -/
@[stacks 07MS]
noncomputable def crystallineStructureBaseChange
    {X' X S' S : RingedSite.{u, v, w}}
    [UnivLE.{max u v, z}]
    (g' : RingedSite.Hom X X') (f' : RingedSite.Hom X' S')
    (f : RingedSite.Hom X S) (g : RingedSite.Hom S S')
    [g'.modulePushforward.{z}.IsRightAdjoint]
    [f'.modulePushforward.{z}.IsRightAdjoint]
    [f.modulePushforward.{z}.IsRightAdjoint]
    [g.modulePushforward.{z}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f') (ModuleQis.{z} X')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} g) (ModuleQis.{z} S')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} g') (ModuleQis.{z} X')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} f) (ModuleQis.{z} S)]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} f') (ModuleQis.{z} S')]
    [DerivedAdjunction.HasPair.{z} f]
    [DerivedAdjunction.HasPair.{z} f']
    (squareIso :
      modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
        modulePullbackDerived.{z} f' ⋙ modulePullbackDerived.{z} g')
    (F' : ModuleDerived.{z} X') (F : ModuleDerived.{z} X)
    (crystallinePullback : (modulePullbackDerived.{z} g').obj F' ⟶ F) :
    (modulePullbackDerived.{z} g).obj ((modulePushforwardDerived.{z} f').obj F') ⟶
      (modulePushforwardDerived.{z} f).obj F :=
  derivedCrystallineBaseChange g' f' f g squareIso F' F crystallinePullback

/-- The sheaf-level crystalline structure-morphism base-change map is the Cohomology on Sites
Remark 21.19.3 mate followed by the crystalline pullback comparison
`L f_cris^* F' ⟶ f_cris^* F' = F`. -/
theorem crystallineStructureBaseChange_spec
    {X' X S' S : RingedSite.{u, v, w}}
    [UnivLE.{max u v, z}]
    (g' : RingedSite.Hom X X') (f' : RingedSite.Hom X' S')
    (f : RingedSite.Hom X S) (g : RingedSite.Hom S S')
    [g'.modulePushforward.{z}.IsRightAdjoint]
    [f'.modulePushforward.{z}.IsRightAdjoint]
    [f.modulePushforward.{z}.IsRightAdjoint]
    [g.modulePushforward.{z}.IsRightAdjoint]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{z} f') (ModuleQis.{z} X')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} g) (ModuleQis.{z} S')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} g') (ModuleQis.{z} X')]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} f) (ModuleQis.{z} S)]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{z} f') (ModuleQis.{z} S')]
    [DerivedAdjunction.HasPair.{z} f]
    [DerivedAdjunction.HasPair.{z} f']
    (squareIso :
      modulePullbackDerived.{z} g ⋙ modulePullbackDerived.{z} f ≅
        modulePullbackDerived.{z} f' ⋙ modulePullbackDerived.{z} g')
    (F' : ModuleDerived.{z} X') (F : ModuleDerived.{z} X)
    (crystallinePullback : (modulePullbackDerived.{z} g').obj F' ⟶ F) :
    crystallineStructureBaseChange g' f' f g squareIso F' F crystallinePullback =
      (DerivedBaseChange.map g' f f' g squareIso F') ≫
        (modulePushforwardDerived.{z} f).map crystallinePullback :=
  sorry

/- Remark 60.24.8 (Base change map) (2): on global sections the sheaf-level map induces
`RΓ(Cris(X'/S'), F') ⊗ᴸ_{A'} A ⟶ RΓ(Cris(X/S), F)` in `D(A)`, as in 60.24.8.1. -/
@[stacks 07MS]
#check crystallineCohomologyBaseChange
