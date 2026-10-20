/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
public import ReasLib.CategoryTheory.Abelian.Functor.CohomologicalDimension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomological dimension of sections on a ringed site

This leaf specializes the generic right-derived-functor predicates to additive module sections
over an object of a ringed site.  In particular, coproduct compatibility is expressed once for
the canonical sections functor instead of being repeated degree by degree in chapter statements.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleCohomology

variable (X : RingedSite.{u, v, w}) [UnivLE.{max u v, z}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]

/-- Module sections over `U` have cohomological dimension at most `d`. -/
@[stacks 0G21 "cohomological-dimension bound over a site object"]
abbrev HasDimensionLE (U : X) (d : ℤ) : Prop :=
  (ModuleSections.Underlying.sections X U).HasCohomologicalDimensionLE d

/-- Module sections over `U` have a uniform finite cohomological-dimension bound. -/
@[stacks 094D "finite cohomological dimension over a site object"]
abbrev HasFiniteDimension (U : X) : Prop :=
  (ModuleSections.Underlying.sections X U).HasFiniteCohomologicalDimension

/-- Every right-derived module-sections functor over `U` preserves coproducts. -/
@[stacks 0G21 "cohomology over a site object commutes with coproducts"]
abbrev PreservesCoproducts (U : X) : Prop :=
  (ModuleSections.Underlying.sections X U).PreservesCoproductsOfRightDerived

end RingedSite.Hom.ModuleCohomology

end
