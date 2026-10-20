module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong.AffineTypes
import StacksCheckRecall

/-!
# Types of the recompletion of an affine formal algebraic space

Completion along a closed subset of the reduction preserves affineness,
McQuillan and Noetherian properties. Countable indexing and adic* are preserved
when the complement is quasi-compact.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace (Points)
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.37.6 (1): Completion of an affine formal algebraic space along a closed subset of its
reduction is affine. -/
@[stacks 0GVV] #check (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.isAffine :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    (R : ReductionData X) (T : Closeds (Points R.space)),
    AffineFormalAlgebraicSpace.IsAffine (Recompletion.functor R T))

/- Lemma 87.37.6 (2): Completion of a McQuillan affine formal algebraic space along a closed
subset of its reduction is McQuillan. -/
@[stacks 0GVV] #check (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.isMcQuillanAffine :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    [IsMcQuillanAffine X]
    (R : ReductionData X) (T : Closeds (Points R.space)),
    IsMcQuillanAffine (Recompletion.functor R T))

/- Lemma 87.37.6 (3): Completion of a countably indexed affine formal algebraic space is countably
indexed when the closed subset has compact complement in its reduction. -/
@[stacks 0GVV] #check (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.isCountablyIndexedAffine :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X]
    [AffineFormalAlgebraicSpace.IsCountablyIndexedAffine X]
    (R : ReductionData X) (T : Closeds (Points R.space))
    (hT : IsCompact (T.compl : Set (Points R.space))),
    AffineFormalAlgebraicSpace.IsCountablyIndexedAffine (Recompletion.functor R T))

/- Lemma 87.37.6 (4): Completion of an adic* affine formal algebraic space is adic* when the
closed subset has compact complement in its reduction. -/
@[stacks 0GVV] #check (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.isAdicStarAffine :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    [IsAdicStarAffine X]
    (R : ReductionData X) (T : Closeds (Points R.space))
    (hT : IsCompact (T.compl : Set (Points R.space))),
    IsAdicStarAffine (Recompletion.functor R T))

/- Lemma 87.37.6 (5): Completion of a Noetherian affine formal algebraic space along a closed
subset of its reduction is Noetherian. -/
@[stacks 0GVV] #check (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.isNoetherianAffine :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X]
    [AffineFormalAlgebraicSpace.IsAffine X]
    [IsNoetherianAffine X]
    (R : ReductionData X) (T : Closeds (Points R.space)),
    IsNoetherianAffine (Recompletion.functor R T))
