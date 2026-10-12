/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Criteria
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.DenseOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.QuasiFinite

/-!
# Extending finiteness from a dense open

A flat proper morphism is finite when its restriction to a dense open is finite and either the
morphism is locally of finite presentation or the open is retrocompact.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsFinite

/-- A flat proper morphism that is finite over a dense open is finite if the morphism is locally
of finite presentation or the open is retrocompact. -/
theorem of_restrict_of_flat {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] (U : S.Opens) (hU_dense : Dense (U : Set S))
    [IsFinite (f ∣_ U)]
    (h_finitePresentation_or_retrocompact :
      LocallyOfFinitePresentation f ∨ IsRetrocompact (U : Set S)) :
    IsFinite f := sorry

end AlgebraicGeometry.IsFinite
