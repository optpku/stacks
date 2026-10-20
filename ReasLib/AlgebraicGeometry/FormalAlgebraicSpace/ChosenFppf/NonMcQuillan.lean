module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.McQuillan

/-!
# Non-McQuillan affine formal algebraic spaces
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- At a sufficiently large chosen big fppf site, there is an affine formal
algebraic space with no directed affine thickening presentation having all
inverse-limit projections on global sections surjective. -/
theorem exists_isAffineFormalAlgebraicSpace_not_isMcQuillan :
    ∃ (𝒮 : ChosenBigFppfSite.{u, u+1}) (S : 𝒮.carrier)
      (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (u+1)))
      (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (u+1))))
      (X : Sheaf (𝒮.bigTopology S) (Type (u+1))),
      IsAffineFormalAlgebraicSpace X ∧ ¬ IsMcQuillan X := sorry

/-- At a sufficiently large chosen big fppf site, there is a representable
morphism of affine formal algebraic spaces whose target is McQuillan and whose
source is not McQuillan. -/
theorem exists_representable_isMcQuillan_source_not :
    ∃ (𝒮 : ChosenBigFppfSite.{u, u+1}) (S : 𝒮.carrier)
      (_ : HasWeakSheafify (𝒮.bigTopology S) (Type (u+1)))
      (_ : HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (u+1))))
      (X Y : Sheaf (𝒮.bigTopology S) (Type (u+1)))
      (_ : IsAffineFormalAlgebraicSpace X) (_ : IsMcQuillan Y) (f : X ⟶ Y),
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable f ∧
        ¬ IsMcQuillan X := sorry

end AlgebraicGeometry
