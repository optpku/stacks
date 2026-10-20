/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

variable {X P : Scheme.{u}} {E : X.Modules}

/-- The kernel of the canonical quotient from the pullback of `E` to the tautological
module of a represented projective bundle. -/
noncomputable def tautologicalKernel (p : P ⟶ X) (hp : Representation p E) : P.Modules :=
  kernel (tautologicalQuotient p hp).hom

/-- The tautological kernel is the categorical kernel of the canonical tautological quotient. -/
theorem tautologicalKernel_def (p : P ⟶ X) (hp : Representation p E) :
    tautologicalKernel p hp = kernel (tautologicalQuotient p hp).hom := sorry

/-- For a projective bundle associated to a rank-`q + 1` module, the tautological
kernel has rank `q`. -/
theorem tautologicalKernel_isFiniteLocallyFreeOfRank (p : P ⟶ X) (hp : Representation p E)
    (q : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E] :
    Scheme.Modules.IsFiniteLocallyFreeOfRank q (tautologicalKernel p hp) := sorry

end AlgebraicGeometry.Scheme.ProjectiveBundle
