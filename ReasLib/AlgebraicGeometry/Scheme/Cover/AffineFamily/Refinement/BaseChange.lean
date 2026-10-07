module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily.Refinement

/-!
# Base change of finite affine-family refinements

This leaf packages the componentwise compatibility data for a refinement to
be the base change of another refinement.  It remains independent of any
particular topology or descent theorem.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

noncomputable section

namespace AffineFamilyOver.Refinement

/-- A refinement between finite affine families is the base change of another
refinement, relative to chosen componentwise base-change identifications of
its source and target families. -/
structure IsBaseChangeOf {S T : Scheme.{u}} {p : T ⟶ S}
    {sourceS targetS : AffineFamilyOver S} {sourceT targetT : AffineFamilyOver T}
    (sourceBaseChange : AffineFamilyOver.IsBaseChangeOf p sourceS sourceT)
    (targetBaseChange : AffineFamilyOver.IsBaseChangeOf p targetS targetT)
    (refinementS : Refinement sourceS targetS)
    (refinementT : Refinement sourceT targetT) where
  /-- The target-index maps commute with the base-change index equivalences. -/
  index_compatible : ∀ j : Fin sourceS.n,
    targetBaseChange.indexEquiv (refinementS.toIndex j) =
      refinementT.toIndex (sourceBaseChange.indexEquiv j)
  /-- The induced morphism between componentwise categorical pullbacks. -/
  pullbackLift : ∀ j : Fin sourceS.n,
    Limits.pullback p (sourceS.map j) ⟶
      Limits.pullback p (targetS.map (refinementS.toIndex j))
  /-- Compatibility of the induced pullback lift with the projection to the new target. -/
  pullbackLift_fst : ∀ j : Fin sourceS.n,
    pullbackLift j ≫ Limits.pullback.fst p (targetS.map (refinementS.toIndex j)) =
      Limits.pullback.fst p (sourceS.map j)
  /-- Compatibility of the induced pullback lift with the projection to the old source chart. -/
  pullbackLift_snd : ∀ j : Fin sourceS.n,
    pullbackLift j ≫ Limits.pullback.snd p (targetS.map (refinementS.toIndex j)) =
      Limits.pullback.snd p (sourceS.map j) ≫ refinementS.lift j
  /-- After transport along the chosen chart isomorphisms, the displayed
refinement agrees with the induced pullback refinement. -/
  lift_compatible : ∀ j : Fin sourceS.n,
    HEq ((sourceBaseChange.componentIso j).hom ≫
      refinementT.lift (sourceBaseChange.indexEquiv j))
      (pullbackLift j ≫ (targetBaseChange.componentIso (refinementS.toIndex j)).hom)

variable {T T' : Scheme.{u}} [IsAffine T']

/-- The componentwise pullback lift of a refinement still factors through the
corresponding pulled-back chart map. -/
theorem pullback_fac {source target : AffineFamilyOver T}
    (refinement : Refinement source target) (g : T' ⟶ T)
    (j : Fin source.n) :
    Limits.pullback.lift
          (Limits.pullback.fst g (source.map j))
          (Limits.pullback.snd g (source.map j) ≫ refinement.lift j)
          (by
            rw [Category.assoc, refinement.fac]
            exact Limits.pullback.condition) ≫
        (target.pullback g).map (refinement.toIndex j) =
      (source.pullback g).map j := sorry

/-- The canonical pullback of a refinement between finite affine families. -/
def pullback {source target : AffineFamilyOver T}
    (refinement : Refinement source target) (g : T' ⟶ T) :
    Refinement (source.pullback g) (target.pullback g) where
  toIndex := refinement.toIndex
  lift := fun j ↦ Limits.pullback.lift
    (Limits.pullback.fst g (source.map j))
    (Limits.pullback.snd g (source.map j) ≫ refinement.lift j)
    (by
      rw [Category.assoc, refinement.fac]
      exact Limits.pullback.condition)
  fac := pullback_fac refinement g

/-- The four compatibility laws for the canonical componentwise base change
of a refinement. -/
theorem pullback_isBaseChangeOf_spec {source target : AffineFamilyOver T}
    (refinement : Refinement source target) (g : T' ⟶ T) :
    (∀ j : Fin source.n,
      (target.pullback_isBaseChangeOf g).indexEquiv (refinement.toIndex j) =
        (refinement.pullback g).toIndex
          ((source.pullback_isBaseChangeOf g).indexEquiv j)) ∧
    (∀ j : Fin source.n,
      (refinement.pullback g).lift j ≫
          Limits.pullback.fst g (target.map (refinement.toIndex j)) =
        Limits.pullback.fst g (source.map j)) ∧
    (∀ j : Fin source.n,
      (refinement.pullback g).lift j ≫
          Limits.pullback.snd g (target.map (refinement.toIndex j)) =
        Limits.pullback.snd g (source.map j) ≫ refinement.lift j) ∧
    (∀ j : Fin source.n,
      HEq (((source.pullback_isBaseChangeOf g).componentIso j).hom ≫
        (refinement.pullback g).lift
          ((source.pullback_isBaseChangeOf g).indexEquiv j))
        ((refinement.pullback g).lift j ≫
          ((target.pullback_isBaseChangeOf g).componentIso
            (refinement.toIndex j)).hom)) := sorry

/-- The canonical pullback refinement, together with its componentwise
base-change comparison to the original refinement. -/
def pullback_isBaseChangeOf {source target : AffineFamilyOver T}
    (refinement : Refinement source target) (g : T' ⟶ T) :
    IsBaseChangeOf (source.pullback_isBaseChangeOf g)
      (target.pullback_isBaseChangeOf g) refinement (refinement.pullback g) where
  index_compatible := (pullback_isBaseChangeOf_spec refinement g).1
  pullbackLift := fun j ↦ (refinement.pullback g).lift j
  pullbackLift_fst := (pullback_isBaseChangeOf_spec refinement g).2.1
  pullbackLift_snd := (pullback_isBaseChangeOf_spec refinement g).2.2.1
  lift_compatible := (pullback_isBaseChangeOf_spec refinement g).2.2.2

end AffineFamilyOver.Refinement

end

end AlgebraicGeometry
