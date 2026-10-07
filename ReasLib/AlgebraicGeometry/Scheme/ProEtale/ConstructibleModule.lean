module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.LocallyClosedReduction
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.Topology.Stratification.Partition
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ModulePullback

/-!
# Constructible sheaves of modules on the small pro-étale site

A sheaf of `Λ`-modules on `X_proétale` is constructible when every affine open admits a
finite constructible locally closed decomposition on which the restriction is locally
constant of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}} {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
variable [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (f : Y ⟶ X) (P : X.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ),
  (baseChange f).op.HasLeftKanExtension P]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify (topology Y) (ModuleCat.{w} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.ProEt),
  HasWeakSheafify ((topology Y).over U) (ModuleCat.{w} Λ)]

/-- A sheaf of `Λ`-modules on the small pro-étale site is constructible when every affine open
admits a finite partition into constructible locally closed subschemes on which the inverse
image is locally constant of finite type. -/
class IsConstructibleModule (F : Sheaf (topology X) (ModuleCat.{w} Λ)) : Prop where
  /-- Affine opens admit finite constructible locally closed strata with finite-type locally
  constant restrictions. -/
  existsAffineStrata :
    ∀ (U : X.Opens), IsAffineOpen U →
      ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
        ∀ (s : Q.toSet),
          Topology.IsConstructible (s : Set U.toScheme) ∧
            let T : LocallyCloseds U.toScheme :=
              ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
            Sheaf.IsFiniteTypeLocallyConstantModule
              (moduleRestrict (LocallyClosedReduction.ι T ≫ U.ι) F)

/-- Unfolding `IsConstructibleModule` recovers the affine stratification criterion. -/
theorem isConstructibleModule_iff (F : Sheaf (topology X) (ModuleCat.{w} Λ)) :
    IsConstructibleModule F ↔
      ∀ (U : X.Opens), IsAffineOpen U →
        ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
          ∀ (s : Q.toSet),
            Topology.IsConstructible (s : Set U.toScheme) ∧
              let T : LocallyCloseds U.toScheme :=
                ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
              Sheaf.IsFiniteTypeLocallyConstantModule
                (moduleRestrict (LocallyClosedReduction.ι T ≫ U.ι) F) :=
  sorry

/-- A locally constant sheaf of finite-type `Λ`-modules is constructible. -/
instance instIsConstructibleModule_of_finiteTypeLocallyConstant
    (F : Sheaf (topology X) (ModuleCat.{w} Λ))
    [Sheaf.IsFiniteTypeLocallyConstantModule F] :
    IsConstructibleModule F :=
  sorry

/-- The affine stratification supplied by a constructible module sheaf. -/
theorem IsConstructibleModule.existsAffineStrata_spec
    (F : Sheaf (topology X) (ModuleCat.{w} Λ)) [IsConstructibleModule F]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
      ∀ (s : Q.toSet),
        Topology.IsConstructible (s : Set U.toScheme) ∧
          let T : LocallyCloseds U.toScheme :=
            ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
          Sheaf.IsFiniteTypeLocallyConstantModule
            (moduleRestrict (LocallyClosedReduction.ι T ≫ U.ι) F) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
