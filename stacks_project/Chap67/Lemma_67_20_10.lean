/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_20_10_Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 67.20.10 (1): for an affine morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` (Stacks writes `f : Y → X`), with `A = f_* 𝒪_X`, the functor `F ↦ f_* F` is an
equivalence from quasi-coherent `𝒪_X`-modules to quasi-coherent `A`-modules. -/
@[stacks 08AI] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.pushforwardAsModule.isEquivalence :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f],
      Functor.IsEquivalence
        (AlgebraicGeometry.AlgebraicSpace.QCoh.pushforwardAsModule f))

/- Lemma 67.20.10 (2): an `A`-module is quasi-coherent as an `𝒪_Y`-module if and only if it
is quasi-coherent as an `A`-module. -/
@[stacks 08AI] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isQuasicoherent_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
      (ℱ : SheafOfModules (pushforwardStructureAlgebra f)),
      ((SheafOfModules.restrictScalars
          (ringedToposHom f).directStructureMap).obj ℱ).IsQuasicoherent ↔
        ℱ.IsQuasicoherent)
