/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ConstructibleModule

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

#check (AlgebraicGeometry.Scheme.ProEt.IsConstructibleModule :
    Sheaf (topology X) (ModuleCat.{w} Λ) → Prop)

#check (AlgebraicGeometry.Scheme.ProEt.isConstructibleModule_iff :
    ∀ (F : Sheaf (topology X) (ModuleCat.{w} Λ)),
      IsConstructibleModule F ↔
      ∀ (U : X.Opens), IsAffineOpen U →
        ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
          ∀ (s : Q.toSet),
            Topology.IsConstructible (s : Set U.toScheme) ∧
              let T : LocallyCloseds U.toScheme :=
                ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
              Sheaf.IsFiniteTypeLocallyConstantModule
                (moduleRestrict (LocallyClosedReduction.ι T ≫ U.ι) F))

#check (AlgebraicGeometry.Scheme.ProEt.instIsConstructibleModule_of_finiteTypeLocallyConstant :
    ∀ (F : Sheaf (topology X) (ModuleCat.{w} Λ))
    [Sheaf.IsFiniteTypeLocallyConstantModule F],
      IsConstructibleModule F)

#check (AlgebraicGeometry.Scheme.ProEt.IsConstructibleModule.existsAffineStrata_spec :
    ∀ (F : Sheaf (topology X) (ModuleCat.{w} Λ)) [IsConstructibleModule F]
    (U : X.Opens) (hU : IsAffineOpen U),
      ∃ (Q : LocallyClosedPartition U.toScheme), Q.toSet.Finite ∧
      ∀ (s : Q.toSet),
        Topology.IsConstructible (s : Set U.toScheme) ∧
          let T : LocallyCloseds U.toScheme :=
            ⟨(s : Set U.toScheme), Q.locallyClosed_of_mem s.property⟩
          Sheaf.IsFiniteTypeLocallyConstantModule
            (moduleRestrict (LocallyClosedReduction.ι T ≫ U.ι) F))

end AlgebraicGeometry.Scheme.ProEt
