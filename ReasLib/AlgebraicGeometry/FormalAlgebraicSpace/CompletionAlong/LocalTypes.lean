/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.CompletionAlong
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction

/-!
# Local properties of completion along a closed subset

Completion preserves local countable indexing and local adic* when the
open-complement inclusion is quasi-compact, and preserves local Noetherianity
along every closed subset of the reduction.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace (Points)

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.Recompletion

/-- Completion of a locally countably indexed formal algebraic space is locally
countably indexed when the open-complement inclusion in its reduction is
quasi-compact. -/
theorem isLocallyCountablyIndexed {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyCountablyIndexed X]
    (R : ReductionData X) (T : Closeds (Points R.space))
    [AlgebraicSpace.QuasiCompact (AlgebraicSpace.OpenSubspace.Construction.ι R.space T.compl)] :
    IsLocallyCountablyIndexed (functor R T)
      (formalSpace := Recompletion.isFormalAlgebraicSpace R T) :=
  sorry

/-- Completion of a locally adic* formal algebraic space is locally adic* when
the open-complement inclusion in its reduction is quasi-compact. -/
theorem isLocallyAdicStar {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyAdicStar X]
    (R : ReductionData X) (T : Closeds (Points R.space))
    [AlgebraicSpace.QuasiCompact (AlgebraicSpace.OpenSubspace.Construction.ι R.space T.compl)] :
    IsLocallyAdicStar (functor R T)
      (formalSpace := Recompletion.isFormalAlgebraicSpace R T) :=
  sorry

/-- Completion of a locally Noetherian formal algebraic space along any closed
subset of its reduction is locally Noetherian. -/
theorem isLocallyNoetherian {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (R : ReductionData X) (T : Closeds (Points R.space)) :
    IsLocallyNoetherian (functor R T)
      (formalSpace := Recompletion.isFormalAlgebraicSpace R T) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.Recompletion
