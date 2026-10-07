module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.2.8

The associated points of a coherent module on a locally Noetherian algebraic
space form a finite set on every quasi-compact open of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules TopologicalSpace
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 71.2.8: let `S` be a scheme, let `X` be a locally Noetherian algebraic space
over `S`, and let `F` be a coherent `𝒪_X`-module. Then `Ass(F) ∩ W` is finite for every
quasi-compact open `W ⊆ |X|`. On a locally Noetherian algebraic space, `Ass(F)` is
`F.weakAss`. -/
@[stacks 0CUN]
theorem associatedPoints_inter_quasiCompactOpen_finite
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (W : Opens |X|) (hW : IsCompact (W : Set |X|)) :
    (F.weakAss ∩ (W : Set |X|)).Finite :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
