module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap110.Lemma_110_75_1_McQuillan

/-!
# A representable morphism of affine formal algebraic spaces with McQuillan target
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- Lemma 110.75.3: there exists a representable morphism `f : X ⟶ Y` of affine
formal algebraic spaces with `Y` McQuillan, but `X` not McQuillan. -/
@[stacks 0CBE]
theorem exists_representable_isMcQuillan_source_not :
    ∃ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
      (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (max u v)))
      (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v))))
      (X Y : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (_ : IsAffineFormalAlgebraicSpace X) (_ : IsMcQuillan Y) (f : X ⟶ Y),
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable f ∧
        ¬ IsMcQuillan X := sorry

end AlgebraicGeometry
