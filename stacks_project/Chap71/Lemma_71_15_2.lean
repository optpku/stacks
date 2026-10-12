/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_20_1_Tensor
public import stacks_project.Chap71.Lemma_71_15_2_Comparison
public import stacks_project.Chap71.Lemma_71_15_2_Fiber

/-!
# Lemma 71.15.2

Vanishing of higher direct images and surjectivity of the stalk-to-fibre
global-sections map after twisting by a sufficiently ample power on a proper
algebraic space over a Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConcreteCategory

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Lemma 71.15.2: let `Y` be a Noetherian scheme, let `X` be an algebraic space over `Y`
whose structure morphism `f : X ⟶ Y` is proper, let `L` be an invertible `𝒪_X`-module, and
let `F` be a coherent `𝒪_X`-module. Let `y` be a point of `Y` such that the scheme-theoretic
fibre `fiber f y` is a scheme, represented by `e : fiber f y ≅ ofOver T`, and such that
the restricted module `moduleOnScheme f y e L` is ample. Then there exists `d0` such that
for all `d ≥ d0` the stalks `R^p f_*(F ⊗ L^{⊗ d})_y` vanish for `p > 0`, and the restriction
map `f_*(F ⊗ L^{⊗ d})_y ⟶ H^0(X_y, F_y ⊗ L_y^{⊗ d})` is surjective. The Lean comparison is
`pushforwardStalkToFiberCohomology` into global sections of
`moduleOnScheme f y e (twist F L d)`; the identification with `F_y ⊗ L_y^{⊗ d}` is the
postponed monoidal comparison `nonempty_iso_moduleOnScheme_twist`. -/
@[stacks 0D39]
theorem exists_twist_stalk_isZero_and_surjective_of_isAmple_fiber
    {Y : Scheme.{u}} [IsNoetherian Y] {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) [Proper f]
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules]
    (L : X.Modules) [isInvertibleObject L] (F : X.Modules) [F.IsCoherent] (y : Y)
    {T : Over Y} (e : fiber f y ≅ ofOver T)
    [Scheme.Modules.Invertible (moduleOnScheme f y e L)]
    [Scheme.Modules.IsAmple (moduleOnScheme f y e L)] :
    ∃ d0 : ℕ, ∀ d, d0 ≤ d →
      (∀ p, 0 < p →
          IsZero (RingedSpace.stalkModuleCat
            (higherDirectImageOnScheme f (twist F L d) p) y)) ∧
        Function.Surjective
          (ConcreteCategory.hom
            (pushforwardStalkToFiberCohomology f (twist F L d) y e)) :=
  sorry
