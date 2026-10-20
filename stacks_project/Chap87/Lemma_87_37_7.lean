module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong.LocalTypes

/-!
# Types of the recompletion of a formal algebraic space

Completion preserves local countable indexing and local adic* under
quasi-compactness of the open-complement inclusion, and preserves local
Noetherianity along every closed subset of the reduction.
-/

open AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace (Points)
open CategoryTheory TopologicalSpace

universe u

/- Lemma 87.37.7 (1): Completion preserves local countable indexing when the
open-complement inclusion in the reduction is quasi-compact. -/
@[stacks 0GVW] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.isLocallyCountablyIndexed :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsLocallyCountablyIndexed X]
      (R : ReductionData X) (T : Closeds (Points R.space))
      [AlgebraicSpace.QuasiCompact (AlgebraicSpace.OpenSubspace.Construction.ι R.space T.compl)],
      IsLocallyCountablyIndexed (Recompletion.functor R T)
        (formalSpace := Recompletion.isFormalAlgebraicSpace R T))

/- Lemma 87.37.7 (2): Completion preserves local adic* when the open-complement
inclusion in the reduction is quasi-compact. -/
@[stacks 0GVW] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.isLocallyAdicStar :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsLocallyAdicStar X]
      (R : ReductionData X) (T : Closeds (Points R.space))
      [AlgebraicSpace.QuasiCompact (AlgebraicSpace.OpenSubspace.Construction.ι R.space T.compl)],
      IsLocallyAdicStar (Recompletion.functor R T)
        (formalSpace := Recompletion.isFormalAlgebraicSpace R T))

/- Lemma 87.37.7 (3): Completion preserves local Noetherianity along every
closed subset of the reduction. -/
@[stacks 0GVW] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.Recompletion.isLocallyNoetherian :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
      (R : ReductionData X) (T : Closeds (Points R.space)),
      IsLocallyNoetherian (Recompletion.functor R T)
        (formalSpace := Recompletion.isFormalAlgebraicSpace R T))
