/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology.Dimension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.QuasiCompact
public import ReasLib.CategoryTheory.Sites.WeaklyContractible.Consequences
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology over weakly contractible site objects

Weak contractibility supplies the vanishing part of the cohomological-dimension criterion, while
quasi-compactness supplies the degree-zero coproduct comparison.  The resulting predicates are
kept independent of any particular compactness theorem.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleCohomology

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [IsGrothendieckAbelian.{w} (RingedSite.ModuleCat.{w} X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [HasSheafify X.siteTopology AddCommGrpCat.{w}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat.{w})]

/-- Lemma 21.51.1 (0946): weak contractibility gives cohomological dimension at most zero for
the underlying module-sections functor. -/
@[stacks 0946 "weakly contractible sections have no higher cohomology"]
theorem hasDimensionLE_zero_of_weaklyContractible
    (U : X) [X.siteTopology.IsWeaklyContractible U] :
    HasDimensionLE X U 0 := sorry

/-- A weakly contractible object has finite module-cohomological dimension. -/
@[stacks 0946 "finite dimension from weak contractibility"]
theorem hasFiniteDimension_of_weaklyContractible
    (U : X) [X.siteTopology.IsWeaklyContractible U] :
    HasFiniteDimension X U := sorry

/-- Lemma 21.52.6 (094E): quasi-compactness and weak contractibility make every right-derived
module-sections functor over `U` preserve coproducts. -/
@[stacks 094E "coproducts over quasi-compact weakly contractible objects"]
theorem preservesCoproducts_of_quasiCompact_weaklyContractible
    (U : X) (hUqc : X.siteTopology.QuasiCompactObject U)
    [X.siteTopology.IsWeaklyContractible U] :
    PreservesCoproducts X U := sorry

end RingedSite.Hom.ModuleCohomology

end
