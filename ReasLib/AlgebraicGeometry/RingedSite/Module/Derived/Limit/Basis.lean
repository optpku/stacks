module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology.Acyclic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Basiswise hypotheses for derived module towers

The predicates in this file are hypotheses about a tower, rather than conclusions tied to a
particular Stacks chapter.  The acyclicity predicate is indexed by an arbitrary category of
stages; the `R¹ lim` predicate is specialized to the sequential inverse systems for which the
Milnor model is available.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleDerived.Limit

variable (X : RingedSite.{u, v, w})

/- The objectwise acyclicity condition is independent of the choice of an inverse-system index.
   Keeping the index abstract makes the same owner usable for filtered and finite-stage towers. -/
@[stacks 0BKY "basiswise higher-cohomology acyclicity"]
def basiswiseAcyclic
    [UnivLE.{max u v, z}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]
    (B : Set X) {I : Type*} [Category I]
    (F : I ⥤ RingedSite.ModuleCat.{z} X) : Prop :=
  ∀ U : X, U ∈ B → ∀ i : I,
    RingedSite.Hom.ModuleSections.IsAcyclicOver X U (F.obj i)

/- The first-derived-limit condition is deliberately stated on the canonical underlying additive
   sections functor, not on the chapter compatibility alias. -/
@[stacks 0BKY "basiswise first-derived-limit vanishing"]
def basiswiseR1Vanishing
    (B : Set X)
    (F : ℕᵒᵖ ⥤ RingedSite.ModuleCat.{z} X) : Prop :=
  ∀ U : X, U ∈ B →
    IsZero
      (SequentialInverseSystem.firstDerivedLimit
        (F ⋙ RingedSite.Hom.ModuleSections.Underlying.sections.{z} X U))

end RingedSite.Hom.ModuleDerived.Limit

end
