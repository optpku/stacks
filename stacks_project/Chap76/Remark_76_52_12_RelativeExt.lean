module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_10_5_Gamma
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_6_Pullback
public import stacks_project.Chap76.Lemma_76_52_4_Relative

/-!
# Relative Ext representation on algebraic spaces

A derived module `L` on `Y` represents the functor
`F ↦ Ext^i_X(K, E ⊗ Lf^* F)` on quasi-coherent coefficients when there are
degreewise Ext isomorphisms, natural in `F` and compatible with connecting maps.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.Pretriangulated
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The derived object `RHom(K, E ⊗ Lf^* F[0])` whose hypercohomology computes
`Ext^i_{𝒪_X}(K, E ⊗^L Lf^* F)`. -/
def relativeExtTarget [MonoidalCategory (ModuleDerived X)]
    [MonoidalClosed (ModuleDerived X)] (f : X ⟶ Y) (K E : ModuleDerived X)
    (F : Modules Y) : ModuleDerived X :=
  (ihom K).obj (E ⊗ (pullback f).obj ((DerivedCategory.singleFunctor (Modules Y) 0).obj F))

/-- `relativeExtTarget` is the derived internal Hom from `K` into
`E ⊗ Lf^* F[0]`. -/
theorem relativeExtTarget_eq [MonoidalCategory (ModuleDerived X)]
    [MonoidalClosed (ModuleDerived X)] (f : X ⟶ Y) (K E : ModuleDerived X)
    (F : Modules Y) :
    relativeExtTarget f K E F =
      (ihom K).obj (E ⊗ (pullback f).obj ((DerivedCategory.singleFunctor (Modules Y) 0).obj F)) :=
  sorry

/-- Induced map on `relativeExtTarget` from a morphism of coefficient modules on `Y`. -/
def relativeExtTargetMap [MonoidalCategory (ModuleDerived X)]
    [MonoidalClosed (ModuleDerived X)] (f : X ⟶ Y) (K E : ModuleDerived X)
    {F F' : Modules Y} (φ : F ⟶ F') :
    relativeExtTarget f K E F ⟶ relativeExtTarget f K E F' :=
  (ihom K).map (E ◁ (pullback f).map ((DerivedCategory.singleFunctor (Modules Y) 0).map φ))

/-- `relativeExtTargetMap` is `ihom K` applied to `E ◁ Lf^*(φ[0])`. -/
theorem relativeExtTargetMap_eq [MonoidalCategory (ModuleDerived X)]
    [MonoidalClosed (ModuleDerived X)] (f : X ⟶ Y) (K E : ModuleDerived X)
    {F F' : Modules Y} (φ : F ⟶ F') :
    relativeExtTargetMap f K E φ =
      (ihom K).map (E ◁ (pullback f).map ((DerivedCategory.singleFunctor (Modules Y) 0).map φ)) :=
  sorry

/-- Connecting map on `Ext^i_{𝒪_X}(K, E ⊗^L Lf^* -)` attached to a short exact
sequence of modules on `Y`. -/
def relativeExtTargetδ [MonoidalCategory (ModuleDerived X)]
    [MonoidalClosed (ModuleDerived X)] (f : X ⟶ Y) (K E : ModuleDerived X)
    (s : ShortComplex (Modules Y))
    (hs : (s.map (HomologicalComplex.single (Modules Y) (up ℤ) 0)).ShortExact)
    (i : ℤ) [(pullback f).CommShift ℤ] [(tensorLeft E).CommShift ℤ]
    [(ihom K).CommShift ℤ] :
    cohomologyAb X (relativeExtTarget f K E s.X₃) i ⟶
      cohomologyAb X (relativeExtTarget f K E s.X₁) (i + 1) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
    ((moduleDerivedGlobalSectionsAb X).mapTriangle.obj
      ((ihom K).mapTriangle.obj
        ((tensorLeft E).mapTriangle.obj
          ((pullback f).mapTriangle.obj (DerivedCategory.triangleOfSES hs)))))
    i (i + 1) rfl

/-- `relativeExtTargetδ` is homology of the internal-Hom triangle of
`E ⊗ Lf^*(s[0])`. -/
theorem relativeExtTargetδ_eq [MonoidalCategory (ModuleDerived X)]
    [MonoidalClosed (ModuleDerived X)] (f : X ⟶ Y) (K E : ModuleDerived X)
    (s : ShortComplex (Modules Y))
    (hs : (s.map (HomologicalComplex.single (Modules Y) (up ℤ) 0)).ShortExact)
    (i : ℤ) [(pullback f).CommShift ℤ] [(tensorLeft E).CommShift ℤ]
    [(ihom K).CommShift ℤ] :
    relativeExtTargetδ f K E s hs i =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
        ((moduleDerivedGlobalSectionsAb X).mapTriangle.obj
          ((ihom K).mapTriangle.obj
            ((tensorLeft E).mapTriangle.obj
              ((pullback f).mapTriangle.obj (DerivedCategory.triangleOfSES hs)))))
        i (i + 1) rfl :=
  sorry

/-- A derived module `L` on `Y` represents relative Ext of `K` against
`E ⊗ Lf^* -` when some comparison family identifies `Ext^i_Y(L, F)` with
`Ext^i_X(K, E ⊗^L Lf^* F)` for quasi-coherent `F`, naturally in `F` and
compatibly with connecting maps. -/
def RepresentsRelativeExt [MonoidalCategory (ModuleDerived X)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived Y)] (f : X ⟶ Y) (K E : ModuleDerived X)
    (L : ModuleDerived Y) : Prop :=
  ∃ α :
    ∀ (F : Modules Y) (_ : quasiCoherentModuleProperty Y F) (i : ℤ),
      cohomologyAb Y ((ihom L).obj ((DerivedCategory.singleFunctor (Modules Y) 0).obj F)) i ⟶
        cohomologyAb X (relativeExtTarget f K E F) i,
    (∀ (F : Modules Y) (hF : quasiCoherentModuleProperty Y F) (i : ℤ),
        IsIso (α F hF i)) ∧
      (∀ {F F' : Modules Y} (φ : F ⟶ F') (hF : quasiCoherentModuleProperty Y F)
          (hF' : quasiCoherentModuleProperty Y F') (i : ℤ),
          α F hF i ≫ cohomologyAb_map (relativeExtTargetMap f K E φ) i =
            cohomologyAb_map ((ihom L).map ((DerivedCategory.singleFunctor (Modules Y) 0).map φ)) i ≫
              α F' hF' i) ∧
        ∀ (s : ShortComplex (Modules Y))
          (hs0 : (s.map (HomologicalComplex.single (Modules Y) (up ℤ) 0)).ShortExact)
          (hF₁ : quasiCoherentModuleProperty Y s.X₁)
          (hF₃ : quasiCoherentModuleProperty Y s.X₃) (i : ℤ)
          [(pullback f).CommShift ℤ] [(tensorLeft E).CommShift ℤ]
          [(ihom K).CommShift ℤ] [(ihom L).CommShift ℤ],
          α s.X₃ hF₃ i ≫ relativeExtTargetδ f K E s hs0 i =
            (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
                ((moduleDerivedGlobalSectionsAb Y).mapTriangle.obj
                  ((ihom L).mapTriangle.obj (DerivedCategory.triangleOfSES hs0)))
                i (i + 1) rfl ≫
              α s.X₁ hF₁ (i + 1)

/-- Pack a degreewise isomorphism family that is natural in quasi-coherent
coefficients and compatible with connecting maps into a relative Ext
representation. -/
theorem RepresentsRelativeExt.of [MonoidalCategory (ModuleDerived X)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived Y)] (f : X ⟶ Y) (K E : ModuleDerived X)
    (L : ModuleDerived Y)
    (α :
      ∀ (F : Modules Y) (_ : quasiCoherentModuleProperty Y F) (i : ℤ),
        cohomologyAb Y ((ihom L).obj ((DerivedCategory.singleFunctor (Modules Y) 0).obj F)) i ⟶
          cohomologyAb X (relativeExtTarget f K E F) i)
    (hIso :
      ∀ (F : Modules Y) (hF : quasiCoherentModuleProperty Y F) (i : ℤ),
        IsIso (α F hF i))
    (hNat :
      ∀ {F F' : Modules Y} (φ : F ⟶ F') (hF : quasiCoherentModuleProperty Y F)
        (hF' : quasiCoherentModuleProperty Y F') (i : ℤ),
        α F hF i ≫ cohomologyAb_map (relativeExtTargetMap f K E φ) i =
          cohomologyAb_map ((ihom L).map ((DerivedCategory.singleFunctor (Modules Y) 0).map φ)) i ≫
            α F' hF' i)
    (hBoundary :
      ∀ (s : ShortComplex (Modules Y))
        (hs0 : (s.map (HomologicalComplex.single (Modules Y) (up ℤ) 0)).ShortExact)
        (hF₁ : quasiCoherentModuleProperty Y s.X₁)
        (hF₃ : quasiCoherentModuleProperty Y s.X₃) (i : ℤ)
        [(pullback f).CommShift ℤ] [(tensorLeft E).CommShift ℤ]
        [(ihom K).CommShift ℤ] [(ihom L).CommShift ℤ],
        α s.X₃ hF₃ i ≫ relativeExtTargetδ f K E s hs0 i =
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
              ((moduleDerivedGlobalSectionsAb Y).mapTriangle.obj
                ((ihom L).mapTriangle.obj (DerivedCategory.triangleOfSES hs0)))
              i (i + 1) rfl ≫
            α s.X₁ hF₁ (i + 1)) :
    RepresentsRelativeExt f K E L :=
  sorry

/-- Representing relative Ext means there is a comparison family that is
invertible in every degree, natural in quasi-coherent coefficients, and
compatible with connecting maps. -/
theorem RepresentsRelativeExt.iff [MonoidalCategory (ModuleDerived X)]
    [MonoidalClosed (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
    [MonoidalClosed (ModuleDerived Y)] (f : X ⟶ Y) (K E : ModuleDerived X)
    (L : ModuleDerived Y) :
    RepresentsRelativeExt f K E L ↔
      ∃ α :
        ∀ (F : Modules Y) (_ : quasiCoherentModuleProperty Y F) (i : ℤ),
          cohomologyAb Y ((ihom L).obj ((DerivedCategory.singleFunctor (Modules Y) 0).obj F)) i ⟶
            cohomologyAb X (relativeExtTarget f K E F) i,
        (∀ (F : Modules Y) (hF : quasiCoherentModuleProperty Y F) (i : ℤ),
            IsIso (α F hF i)) ∧
          (∀ {F F' : Modules Y} (φ : F ⟶ F') (hF : quasiCoherentModuleProperty Y F)
              (hF' : quasiCoherentModuleProperty Y F') (i : ℤ),
              α F hF i ≫ cohomologyAb_map (relativeExtTargetMap f K E φ) i =
                cohomologyAb_map ((ihom L).map ((DerivedCategory.singleFunctor (Modules Y) 0).map φ)) i ≫
                  α F' hF' i) ∧
            ∀ (s : ShortComplex (Modules Y))
              (hs0 :
                (s.map (HomologicalComplex.single (Modules Y) (up ℤ) 0)).ShortExact)
              (hF₁ : quasiCoherentModuleProperty Y s.X₁)
              (hF₃ : quasiCoherentModuleProperty Y s.X₃) (i : ℤ)
              [(pullback f).CommShift ℤ] [(tensorLeft E).CommShift ℤ]
              [(ihom K).CommShift ℤ] [(ihom L).CommShift ℤ],
              α s.X₃ hF₃ i ≫ relativeExtTargetδ f K E s hs0 i =
                (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
                    ((moduleDerivedGlobalSectionsAb Y).mapTriangle.obj
                      ((ihom L).mapTriangle.obj (DerivedCategory.triangleOfSES hs0)))
                    i (i + 1) rfl ≫
                  α s.X₁ hF₁ (i + 1) :=
  sorry

/-- For a proper, flat, finitely presented morphism with quasi-compact
quasi-separated target, relative Ext of a pseudo-coherent complex against a
`Y`-perfect complex has a pseudo-coherent representative on `Y`. -/
theorem existsPseudoCoherentRelativeExtRepresentation (f : X ⟶ Y)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [Proper f] [Flat f] [FinitePresentation f]
    [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived Y)] [MonoidalClosed (ModuleDerived Y)]
    (E K : ModuleDerived X) (hE : IsPerfectRelativeTo f E)
    (hK : IsPseudoCoherent X K) :
    ∃ L : ModuleDerived Y, IsPseudoCoherent Y L ∧ RepresentsRelativeExt f K E L :=
  sorry

/-- Any two pseudo-coherent representatives of the same relative Ext functor are
isomorphic in `D(𝒪_Y)`. -/
theorem relativeExtRepresentation_unique (f : X ⟶ Y)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [Proper f] [Flat f] [FinitePresentation f]
    [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
    [MonoidalCategory (ModuleDerived Y)] [MonoidalClosed (ModuleDerived Y)]
    (E K : ModuleDerived X) (hE : IsPerfectRelativeTo f E)
    (hK : IsPseudoCoherent X K) (L L' : ModuleDerived Y)
    (hL : IsPseudoCoherent Y L) (hL' : IsPseudoCoherent Y L')
    (representsL : RepresentsRelativeExt f K E L)
    (representsL' : RepresentsRelativeExt f K E L') :
    IsIsomorphic L L' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
