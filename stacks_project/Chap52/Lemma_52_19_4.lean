/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_14_2
public import stacks_project.Chap52.Definition_52_19_1
public import stacks_project.Chap52.Lemma_52_16_3_Instances
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import Mathlib.Topology.Irreducible
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Set TopologicalSpace
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- Lemma 52.19.4: in Situation 52.16.1, suppose `d ≥ 1`, the ring `A` is
`S.I`-adically complete and has a dualizing complex, and `cd(A, S.I) ≤ d`.
If the completion of a coherent module `F` satisfies the strict `(1, 1 + d)`-
inequalities, and `closure {x} ∩ Set.range S.y` has irreducible components both
contained and not contained in `Set.range S.z`, then `x` lies in `S.U` and the
stalk `F_x` has depth at least one. -/
@[stacks 0EJ5]
theorem moduleDepth_stalk_ge_one_of_mixed_components
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    [IsAdicComplete S.I A]
    (d : ℤ) (hd : 1 ≤ d)
    (h_cd : Ideal.LocalCohomology.HasDimensionLE S.I d)
    (F : RingedSpace.Coh (S.U.toScheme).toRingedSpace)
    (h_strict : SatisfiesStrictInequalities S
      ((CoherentCompletion.functor
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)).obj F)
      1 (1 + d))
    (x : S.X)
    (h_components :
      let WY := closure ({x} : Set S.X) ∩ Set.range S.y
      ∃ W_in W_out : Set S.X,
        Maximal (fun C ↦ IsIrreducible C ∧ C ⊆ WY) W_in ∧
          Maximal (fun C ↦ IsIrreducible C ∧ C ⊆ WY) W_out ∧
            W_in ⊆ Set.range S.z ∧ ¬ W_out ⊆ Set.range S.z) :
    ∃ hx : x ∈ S.U,
      (1 : ℕ∞) ≤ moduleDepth ((S.U.toScheme).presheaf.stalk ⟨x, hx⟩)
        (RingedSpace.stalkModuleCat F.obj ⟨x, hx⟩) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
