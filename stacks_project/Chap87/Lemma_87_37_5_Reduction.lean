/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_37_4_Completion
public import stacks_project.Chap66.Definition_66_12_5_Reduced

/-!
# Reduction of the completion along a closed subset

The algebraic-space reduction of `completionAlong X T` is the reduced induced
closed subspace of `reduction X` on `T`, via the comparison morphism
`fromReduced`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace (Points ClosedSubspaceStructure)

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The composite of the reduced induced inclusion of `T` with `reductionι X`
maps into `T`. -/
theorem mapsInto_fromReduced {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) {U : Over S}
    (z : ((ClosedSubspaceStructure.reduced T).space.functorOfPoints).obj (op U)) :
    mapsInto (T : Set (Points (reduction X)))
      ((NatTrans.vcomp (ClosedSubspaceStructure.reduced T).ι (reductionι X)).app
        (op U) z) :=
  sorry

namespace completionAlong

/-- The canonical morphism from the reduced induced closed subspace on `T` into
the completion of `X` along `T`. -/
def fromReduced {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) :
    (ClosedSubspaceStructure.reduced T).space.functorOfPoints ⟶
      completionAlong X T where
  app U :=
    ofHom fun z ↦
      ⟨(NatTrans.vcomp (ClosedSubspaceStructure.reduced T).ι (reductionι X)).app
          U z,
        mapsInto_fromReduced T z⟩
  naturality := sorry

/-- Postcomposing `fromReduced T` with `ι X T` recovers the composite of the
reduced induced inclusion of `T` with `reductionι X`. -/
theorem fromReduced_comp_ι {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) :
    fromReduced T ≫ ι X T =
      NatTrans.vcomp (ClosedSubspaceStructure.reduced T).ι (reductionι X) :=
  sorry

end completionAlong

/-- The canonical reduction of `completionAlong X T` is the reduced induced
closed subspace of `reduction X` on `T`. -/
instance instReduction_completionAlong {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] [Reduction X]
    (T : Closeds (Points (reduction X))) :
    Reduction (completionAlong X T) where
  space := (ClosedSubspaceStructure.reduced T).space
  ι := completionAlong.fromReduced T
  isReduced := sorry
  representable := sorry
  isThickening := sorry
  liftUnique := sorry

end AlgebraicGeometry.FormalAlgebraicSpace
