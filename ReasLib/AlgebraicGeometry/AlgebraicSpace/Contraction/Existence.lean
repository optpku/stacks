/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Solution
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Separation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.RingTheory.Regular.GRing

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Over a locally Noetherian scheme with G-ring stalks at finite type points,
a contraction situation whose algebraic space and formal algebraic space are
quasi-separated over the base admits a solution locally of finite type over
the base. -/
theorem exists_solutionFor_of_quasiSeparated (σ : ContractionSituation S)
    [QuasiSeparated (toBase σ.X')] [FormalAlgebraicSpace.QuasiSeparated (toBaseW σ)]
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X)),
      Nonempty (SolutionFor σ X) :=
  sorry

/-- Over a locally Noetherian scheme with G-ring stalks at finite type points,
a quasi-separated contraction situation admits a locally finite type solution
whose morphism is proper, whose completion comparison is an isomorphism,
whose closed subset has the prescribed inverse image, and whose morphism is
an isomorphism over the open complement, with the prescribed commutativity
on completions. -/
theorem exists_solutionFor_of_quasiSeparated_spec (σ : ContractionSituation S)
    [QuasiSeparated (toBase σ.X')] [FormalAlgebraicSpace.QuasiSeparated (toBaseW σ)]
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X))
      (sol : SolutionFor σ X),
      Proper sol.f ∧ IsIso sol.a ∧
        σ.T' = sol.T.preimage (Points.continuous_map sol.f) ∧
        IsIsoOverOpen sol.f (AlgebraicSpace.openComplementι X sol.T) ∧
        sol.mapCompletion ≫ sol.a = σ.g :=
  sorry

/-- Over a locally Noetherian scheme with G-ring stalks at finite type points,
a contraction situation whose algebraic space and formal algebraic space are
separated over the base admits a solution locally of finite type over the
base. -/
@[stacks 0GIB]
theorem exists_solutionFor (σ : ContractionSituation S)
    [Separated (toBase σ.X')] [FormalAlgebraicSpace.Separated (toBaseW σ)]
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X)),
      Nonempty (SolutionFor σ X) :=
  exists_solutionFor_of_quasiSeparated σ hG

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
