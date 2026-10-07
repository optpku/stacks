module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.SiteExtComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ExactRightComposition
public import stacks_project.Chap64.Remark_64_29_2_Cohomology

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.AmbientGeometry
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable (X : SchemeOverField k) [CompactSpace X.left] [QuasiSeparatedSpace X.left]

/-- The actual geometric Galois pullback action on sections, functorially on
ARITHMETIC SHEAVES. No fundamental group or group-cohomology comparison occurs here. -/
def geometricSheafSectionsAction :
    Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  obj F :=
    { V := (sections Λ).obj ((modulePullback Λ (geometricToArithmeticHom X)).obj F)
      ρ := { toFun := fun σ ↦ geometricSectionsEnd Λ X σ F
             map_one' := geometricSectionsEnd_one Λ X F
             map_mul' := fun σ τ ↦ geometricSectionsEnd_mul Λ X σ τ F } }
  map f := { hom := (sections Λ).map ((modulePullback Λ (geometricToArithmeticHom X)).map f)
             comm := fun _ ↦ sorry }
  map_id := sorry
  map_comp := sorry

/-- The geometric sheaf-section action functor is additive. -/
instance geometricSheafSectionsAction_additive : (geometricSheafSectionsAction Λ X).Additive := sorry

/-- Geometric inverse image of module sheaves is additive. -/
instance geometricModulePullback_additive : (modulePullback Λ (geometricToArithmeticHom X)).Additive := sorry

/-- Geometric inverse image is exact. -/
instance geometricModulePullback_preservesFiniteLimits :
    PreservesFiniteLimits (modulePullback Λ (geometricToArithmeticHom X)) := sorry

/-- Geometric inverse image preserves finite colimits. -/
instance geometricModulePullback_preservesFiniteColimits :
    PreservesFiniteColimits (modulePullback Λ (geometricToArithmeticHom X)) := sorry

variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ))]

/-- The independently constructed geometric action is derived on arithmetic sheaves. -/
def geometricSheafDerivedAction (n : ℕ) := (geometricSheafSectionsAction Λ X).rightDerived n

/-- Its underlying degree-zero functor is the actual geometric inverse image followed by sections. -/
def geometricSheafSectionsUnderlyingIso :
    geometricSheafSectionsAction Λ X ⋙ Action.forget (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) ≅
      modulePullback Λ (geometricToArithmeticHom X) ⋙ sections (X := geometricBaseChange X) Λ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- For qcqs X and finite coefficients, geometric inverse image of an arithmetic
injective sheaf is sections-acyclic, by continuity through finite field extensions.
This does not assert injective preservation by an arbitrary inverse-image functor. -/
theorem geometricPullback_injective_acyclic
    (I : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hI : Injective I) (n : ℕ) :
    IsZero (((sections (X := geometricBaseChange X) Λ).rightDerived (n + 1)).obj
      ((modulePullback Λ (geometricToArithmeticHom X)).obj I)) := sorry

variable [HasSheafify (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]

/-- The underlying geometric derived action maps to the ACTUAL site-Ext
cohomology through resolution lifts and Ext-class evaluation, independently of group cohomology. -/
def geometricSheafDerivedSiteIso (n : ℕ) :
    geometricSheafDerivedAction Λ X n ⋙ Action.forget (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) ≅
      modulePullback Λ (geometricToArithmeticHom X) ⋙
        siteModuleCohomologyModuleFunctor (J := (geometricBaseChange X).smallEtaleTopology) (A := Λ) n :=
  (Functor.RightDerived.postcompIso (geometricSheafSectionsAction Λ X)
      (Action.forget (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k)) n).symm ≪≫
    NatIso.rightDerived (geometricSheafSectionsUnderlyingIso Λ X) n ≪≫
    ActualExactRightComposition.isoOfAcyclic (modulePullback Λ (geometricToArithmeticHom X))
      (sections (X := geometricBaseChange X) Λ) (geometricPullback_injective_acyclic Λ X) n ≪≫
    Functor.isoWhiskerLeft (modulePullback Λ (geometricToArithmeticHom X))
      (ActualSiteExt.moduleToSiteNatIso (geometricBaseChange X) Λ n)

/-- The actual geometric site cohomology receives its Galois action solely from
geometric pullback/descent and the specified geometric resolution/Ext comparison. -/
def geometricSiteGaloisAction (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  V := geometricModuleEtaleHq X F n
  ρ := (((geometricSheafDerivedSiteIso Λ X n).app F).conj.toMonoidHom).comp
    ((geometricSheafDerivedAction Λ X n).obj F).ρ

end AlgebraicGeometry.SchemeOverField.AmbientGeometry
