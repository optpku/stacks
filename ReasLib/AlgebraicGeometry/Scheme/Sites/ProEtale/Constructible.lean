module

public import ReasLib.AlgebraicGeometry.Scheme.LocallyClosedReduction
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.Topology.Stratification.Partition
public import Mathlib.Topology.Constructible
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open TopologicalSpace
open Topology

universe u v w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}}

/-- A sheaf on the small pro-étale site is constructible relative to a supplied local-constancy
predicate when every affine open admits a finite partition into constructible locally closed
subschemes on which the corresponding restrictions satisfy that predicate. -/
def IsConstructibleProEtale
    {D : Type w} [Category.{v} D]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf (ProEt.topology X) D → Sheaf (ProEt.topology Y) D)
    (locallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf (ProEt.topology Y) D → Prop)
    (F : Sheaf (ProEt.topology X) D) : Prop :=
  ∀ (U : X.Opens), IsAffineOpen U →
    ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
      ∀ (s : Q.toSet),
        Topology.IsConstructible (s : Set U.toScheme) ∧
          let T : LocallyCloseds U.toScheme :=
            ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
          locallyConstant (restrict (Scheme.LocallyClosedReduction.ι T ≫ U.ι) F)

/-- The predicate `IsConstructibleProEtale` is equivalent to its affine finite-stratification
criterion. -/
theorem isConstructibleProEtale_iff
    {D : Type w} [Category.{v} D]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf (ProEt.topology X) D → Sheaf (ProEt.topology Y) D)
    (locallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf (ProEt.topology Y) D → Prop)
    (F : Sheaf (ProEt.topology X) D) :
    IsConstructibleProEtale restrict locallyConstant F ↔
      ∀ (U : X.Opens), IsAffineOpen U →
        ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
          ∀ (s : Q.toSet),
            Topology.IsConstructible (s : Set U.toScheme) ∧
              let T : LocallyCloseds U.toScheme :=
                ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
              locallyConstant (restrict (Scheme.LocallyClosedReduction.ι T ≫ U.ι) F) := sorry

/-- For a Noetherian ring `Λ`, a module-valued pro-étale sheaf is constructible when its
restrictions to constructible locally closed strata are of finite type and locally constant. -/
abbrev IsConstructibleProEtaleModule
    {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
    (restrict : ∀ {Y : Scheme.{u}} (_ : Y ⟶ X),
      Sheaf (ProEt.topology X) (ModuleCat.{w} Λ) →
        Sheaf (ProEt.topology Y) (ModuleCat.{w} Λ))
    (finiteTypeLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf (ProEt.topology Y) (ModuleCat.{w} Λ) → Prop)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{w} Λ)) : Prop :=
  IsConstructibleProEtale restrict finiteTypeLocallyConstant F

end CategoryTheory.Sheaf
