/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import stacks_project.Chap57.Lemma_57_12_4
public import stacks_project.Chap57.Lemma_57_12_5_PullbackTensor
public import stacks_project.Chap57.Lemma_57_12_5_Siblings

import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.SchemeOverField.PerfectDerived

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- Lemma 57.12.5: for a field `k` and a proper regular `k`-scheme `X`, a `k`-linear exact
endofunctor `F` of `PerfectDerived X` that is isomorphic to the identity on every coherent
`𝒪_X`-module of support dimension `0` is sibling to some `F'` of the form
`M ↦ Lf^* M ⊗^L L`, for an automorphism `f` of `X` over `k` that induces the identity on
the underlying topological space and an invertible `𝒪_X`-module `L`. -/
@[stacks 0G27]
theorem exists_idOnSpace_automorphism_invertible_areSiblings
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Regular X.left]
    (F : PerfectDerived X ⥤ PerfectDerived X) [F.Linear k] [F.CommShift ℤ]
    (h_exact : F.HasTriangulatedStructure)
    (hF : ∀ (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ],
      topologicalKrullDim (moduleSupport ℱ) = 0 →
        Nonempty (ofCoherentModule X ℱ ≅ F.obj (ofCoherentModule X ℱ))) :
    ∃ (φ : X ⟶ X) (_ : IsIso φ),
      IsIdentityOnUnderlyingSpace ((Over.forget _).map φ) ∧
        ∃ (L : X.left.Modules) (_ : Scheme.Modules.Invertible L),
          areSiblings F (pullbackTensorInvertible ((Over.forget _).map φ) L) h_exact
            (pullbackTensorInvertible_hasTriangulatedStructure
              ((Over.forget _).map φ) L) := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
