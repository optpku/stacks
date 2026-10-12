/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_29_4_Stalk
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap69.Lemma_69_22_7_Neighbourhood

/-!
# Lemma 69.22.8

Positive higher direct images of a coherent module along a proper morphism of
algebraic spaces have vanishing geometric stalks over a locally Noetherian
target, whenever the geometric fibre is discrete.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalFunctions
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.FormalFunctions

/-- Lemma 69.22.8: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `ȳ` be a geometric point of `Y`. Assume `Y` locally Noetherian,
`f` is proper, and the geometric fibre `fiber f ȳ` has discrete space of points.
Then for any coherent sheaf `F` on `X`, the geometric stalk
`stalkModuleCat ȳ (higherDirectImage f F p)` is zero for all `p > 0`. -/
@[stacks 0A4S]
theorem stalkModuleCat_higherDirectImage_isZero_of_discreteFiber
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Proper f]
    (F : X.Modules) [F.IsCoherent] (ybar : GeometricPoint Y)
    [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules]
    (h_discrete : DiscreteTopology (Points (fiber f ybar)))
    (p : ℕ) (hp : 0 < p) :
    IsZero (stalkModuleCat ybar (Modules.higherDirectImage f F p)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormalFunctions
