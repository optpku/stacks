/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization
public import ReasLib.CategoryTheory.Sites.EnoughObjects
import Mathlib.Tactic.CrossRefAttribute

/-!
# Acyclic cohomology sheaves over objects of a ringed site

This file owns only the reusable objectwise acyclicity predicates.  Their canonical definition
uses ordinary right-derived vanishing for the additive sections functor; a source-facing
cohomology characterization is provided as glue.  The unbounded comparison theorem lives in the
sibling `Acyclic.Comparison` leaf, where its truncation-limit dependencies are explicit.
-/

@[expose] public section

-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

open CategoryTheory CategoryTheory.Limits Opposite
open scoped RingedSiteCohomology

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleSections

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{max u v, z}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]

/-- A module sheaf is acyclic over `U` when its strictly positive objectwise cohomology
vanishes. -/
@[stacks 0BKZ "objectwise acyclic module sheaf"]
def IsAcyclicOver (U : X) (F : RingedSite.ModuleCat.{z} X) : Prop :=
  Functor.RightDerived.Vanishes.aboveZero (Underlying.sections.{z} X U) F

/-- Objectwise acyclicity is equivalent to vanishing of the positive cohomology groups of the
associated degree-zero derived module. -/
@[stacks 0BKZ "objectwise acyclicity cohomology characterization"]
theorem isAcyclicOver_iff_cohomology_isZero (U : X) (F : RingedSite.ModuleCat.{z} X) :
    IsAcyclicOver X U F ↔
      ∀ p : ℤ, 0 < p →
        IsZero
          (RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X U
            ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)).obj F) p) :=
  sorry

/-- An objectwise acyclic module sheaf has zero positive cohomology over the chosen object. -/
@[stacks 0BKZ "positive cohomology of an objectwise acyclic module sheaf"]
theorem IsAcyclicOver.cohomology_isZero {U : X} {F : RingedSite.ModuleCat.{z} X}
    (hF : IsAcyclicOver X U F) (p : ℤ) (hp : 0 < p) :
    IsZero
      (RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X U
        ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)).obj F) p) := sorry

/-- A module sheaf is acyclic on `B` when it is acyclic over every object in `B`. -/
@[stacks 0BKZ "acyclic module sheaf on an object family"]
def IsAcyclicOn (B : Set X) (F : RingedSite.ModuleCat.{z} X) : Prop :=
  ∀ ⦃U : X⦄, U ∈ B → IsAcyclicOver X U F

/-- Acyclicity on an object family specializes to any member of the family. -/
@[stacks 0BKZ "objectwise specialization of family acyclicity"]
theorem IsAcyclicOn.over {B : Set X} {F : RingedSite.ModuleCat.{z} X}
    (hF : IsAcyclicOn X B F) {U : X} (hU : U ∈ B) :
    IsAcyclicOver X U F := sorry

end RingedSite.Hom.ModuleSections

namespace RingedSite.Hom.ModuleDerived.CohomologySheaves

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{max u v, z}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]

/-- The degree-`q` cohomology sheaf of `K`, regarded as a derived module concentrated in
degree zero. -/
@[stacks 0BKZ "cohomology sheaf concentrated in degree zero"]
abbrev asDerived (K : RingedSite.Hom.ModuleDerived.{z} X) (q : ℤ) :
    RingedSite.Hom.ModuleDerived.{z} X :=
  (DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)).obj
    (RingedSite.Hom.ModuleDerived.cohomologySheaf.{z} X K q)

/-- Every cohomology sheaf of `K` is objectwise acyclic on `B`. -/
@[stacks 0BKZ "acyclic cohomology sheaves on an object family"]
def IsAcyclicOn (B : Set X) (K : RingedSite.Hom.ModuleDerived.{z} X) : Prop :=
  ∀ q : ℤ,
    RingedSite.Hom.ModuleSections.IsAcyclicOn X B
      (RingedSite.Hom.ModuleDerived.cohomologySheaf.{z} X K q)

/-- Acyclicity of all cohomology sheaves specializes to one degree and one member of `B`. -/
@[stacks 0BKZ "degreewise objectwise acyclicity"]
theorem IsAcyclicOn.over {B : Set X} {K : RingedSite.Hom.ModuleDerived.{z} X}
    (hK : IsAcyclicOn X B K) (q : ℤ) {U : X} (hU : U ∈ B) :
    RingedSite.Hom.ModuleSections.IsAcyclicOver X U
      (RingedSite.Hom.ModuleDerived.cohomologySheaf.{z} X K q) := sorry

end RingedSite.Hom.ModuleDerived.CohomologySheaves

end
