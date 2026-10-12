/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Neighborhood

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

variable {X : Scheme.{u}} [IsNoetherian X]

#check (compactSupport : X.IdealSheafData → Compacts X)
#check (neighborhoodSectionsDiagram :
  (I : X.IdealSheafData) → X.Modules → (compactSupport I).openNhdsᵒᵖ ⥤ Type u)
#check (neighborhoodQuotientSectionsDiagram :
  (I : X.IdealSheafData) → X.Modules → ℕ → (compactSupport I).openNhdsᵒᵖ ⥤ Type u)
#check (neighborhoodComparison :
  (I : X.IdealSheafData) → (M : X.Modules) →
    colimit (neighborhoodSectionsDiagram I M) ⟶
      limit (positiveNeighborhoodSectionsSystem I M))
#check (NeighborhoodCompletionFullyFaithful : X.IdealSheafData → Prop)

end AlgebraicGeometry.Scheme.CoherentCompletion
