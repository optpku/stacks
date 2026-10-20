module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap71.Lemma_71_4_6_Fiber
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin
public import stacks_project.Chap71.Lemma_71_4_6_Tensor
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Lemma 71.4.6

The associated points of the tensor of a quasi-coherent module flat over the
target with the pullback of a quasi-coherent module are the relative associated
points lying over associated points of the base module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace relativeAssassin

/-- Lemma 71.4.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Let `G`
be a quasi-coherent `𝒪_Y`-module. Assume `F` is flat over `Y`, `X` and `Y` are
locally Noetherian, and the fibres of `f` are locally Noetherian. Then
`Ass_X(F ⊗_{𝒪_X} f^* G) = {x ∈ Ass_{X/Y}(F) | f(x) ∈ Ass_Y(G)}`.
On locally Noetherian algebraic spaces, `Ass` is `weakAss`; under locally
Noetherian fibres, `Ass_{X/Y}(F)` is `relativeAssassin f F`.
`F` is flat over `Y` when it is flat over `Y` at every point of `|X|`. -/
@[stacks 0CV1]
theorem associatedPoints_tensor_pullback_eq_inter_preimage
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hflat : ∀ x : Points X, flatOverAt F f x)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyNoetherianFibers f] :
    (tensorPullback F f G).weakAss =
      relativeAssassin f F ∩ Points.map f ⁻¹' G.weakAss :=
  sorry

/-- A point of `|X|` is associated to `tensorPullback F f G` if and only if it
lies in the relative assassin of `F` over `Y` and its image is associated to
`G`. -/
theorem mem_associatedPoints_tensor_pullback_iff
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hflat : ∀ x : Points X, flatOverAt F f x)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyNoetherianFibers f] (x : Points X) :
    x ∈ (tensorPullback F f G).weakAss ↔
      x ∈ relativeAssassin f F ∧ Points.map f x ∈ G.weakAss :=
  sorry

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
