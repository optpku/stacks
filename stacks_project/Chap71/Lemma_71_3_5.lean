module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated
public import stacks_project.Chap71.Lemma_71_3_5_FieldExtension

/-!
# Lemma 71.3.5

Weak association of a point to a quasi-coherent module on an algebraic space
descends along the projection from a field-extension base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.FieldExtension

/-- Lemma 71.3.5: Let `K/k` be a field extension. Let `X` be an algebraic space
over `k`. Let `F` be a quasi-coherent `𝒪_X`-module. Let `y` be a point of
`AlgebraicSpace.FieldExtension.baseChange k K X` with image `x` in `X`. If `y`
is a weakly associated point of the pullback `baseChange k K F`, then `x` is a
weakly associated point of `F`. -/
@[stacks 0CUS]
theorem mem_weakAss_of_mem_weakAss
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (F : X.Modules)
    [F.IsQuasicoherent]
    (y : Points (AlgebraicSpace.FieldExtension.baseChange k K X))
    (hy : y ∈ (baseChange k K F).weakAss) :
    Points.map (AlgebraicSpace.FieldExtension.toSource k K X) y ∈ F.weakAss :=
  sorry

/-- The image of the weakly associated locus of a field-extension pullback is
contained in the weakly associated locus of the original quasi-coherent module. -/
theorem weakAss_map_subset
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} (F : X.Modules)
    [F.IsQuasicoherent] :
    Points.map (AlgebraicSpace.FieldExtension.toSource k K X) ''
        (baseChange k K F).weakAss ⊆ F.weakAss :=
  sorry

end FieldExtension
end Modules
end AlgebraicSpace
end AlgebraicGeometry
