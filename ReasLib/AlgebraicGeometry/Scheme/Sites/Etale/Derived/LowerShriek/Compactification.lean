/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.ModuleExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pushforward.Additive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale

/-!
# Canonical transitions between compactification models of derived lower shriek
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace etaleDerivedLowerShriek

section ExtensionByZero

variable (Λ : Type u) [Ring Λ]
variable {U T : Scheme.{u}} (j : U ⟶ T) [Etale j] [LocallyQuasiFinite j]
variable [HasSheafCompose U.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose T.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction j).op]
variable [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
variable [T.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

-- Local declaration justification (metaprogramming implementation): expose the private
-- exact functor identification for use in public definitions in this module.
set_option backward.privateInPublic true in
/-- Exact extension by zero and exact finite-support shriek induce the actual derived isomorphism. -/
private def extensionByZeroDerivedIsoLowerShriekModule
    [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ V : U.Etale, HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [∀ V : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
    [(etaleExtensionByZero j (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ))] :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory ≅
      lowerShriekModuleDerived j Λ :=
  Functor.MapDerivedCategory.functorIso (lowerShriekModuleIsoExtensionByZero j Λ)

end ExtensionByZero

variable {Y : Scheme.{u}} {X : Over Y}

-- Local declaration justification (metaprogramming implementation): expose the private
-- triangle equality for equality transport in public definitions in this module.
set_option backward.privateInPublic true in
/-- A morphism of compactifications commutes with the structure maps to `Y`. -/
private theorem ambientMap_comp_structure {P Q : Of Y X} (φ : P ⟶ Q) :
    Of.ambientMap φ ≫ Q.obj.right.hom = P.obj.right.hom :=
  Over.w φ.hom.right

/-- A morphism of compactifications is proper, by cancellation of properness
over `Y`. -/
instance instIsProper_ambientMap {P Q : Of Y X} (φ : P ⟶ Q) :
    IsProper (Of.ambientMap φ) :=
  sorry

variable (X) (Λ : Type u) [Ring Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable {P Q : Of Y X} (φ : P ⟶ Q)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Q.obj.right.left.Etale,
  HasWeakSheafify (Q.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [HasSheafCompose X.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose P.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose Q.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Q.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P)).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι Q)).op]
variable [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]

-- Local declaration justification (metaprogramming implementation): the exposed comparison
-- uses the private exact extension-by-zero identification without adding a public API.
set_option backward.privateInPublic true in
/-- The derived interior comparison is the proper-triangle map transported
along the exact extension-by-zero identifications. -/
def derivedInteriorComparison :
    (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ)).mapDerivedCategory ⟶
      (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward (Of.ambientMap φ) :
          DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  (extensionByZeroDerivedIsoLowerShriekModule Λ (Of.ι Q)).hom ≫
    etaleDerivedLowerShriekProper (Of.ι P) (Of.ambientMap φ)
      (Of.ι_comp_ambientMap φ) Λ ≫
    (isoWhiskerRight (extensionByZeroDerivedIsoLowerShriekModule Λ (Of.ι P)).symm
      (etaleDerivedPushforward (Of.ambientMap φ))).hom

/-- The cochain unit for the genuine iterated derived direct images Rg_* ⋙ Rq_*.
It applies the q-unit and then the g-unit, after the canonical termwise-composition iso. -/
def pushforwardLerayUnit :
    RightDerived.Cochain.toDerived
      (etaleModulePushforward (Of.ambientMap φ) Λ ⋙
        etaleModulePushforward Q.obj.right.hom Λ) ⟶
      (DerivedCategory.Q :
        CochainComplex (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        ((etaleDerivedPushforward (Of.ambientMap φ) :
          DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
            (etaleDerivedPushforward Q.obj.right.hom :
              DerivedCategory (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))) :=
  (isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (etaleModulePushforward (Of.ambientMap φ) Λ ⋙
        etaleModulePushforward Q.obj.right.hom Λ)) (ComplexShape.up ℤ)).symm
    (DerivedCategory.Q :
      CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).hom ≫
    (Functor.associator
      ((etaleModulePushforward (Of.ambientMap φ) Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      ((etaleModulePushforward Q.obj.right.hom Λ).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).hom ≫
    RightDerived.Composition.iteratedUnit
      (RightDerived.Cochain.unit (etaleModulePushforward (Of.ambientMap φ) Λ))
      (RightDerived.Cochain.unit (etaleModulePushforward Q.obj.right.hom Λ))

/-- Étale inverse image is exact, so direct image preserves K-injectives.
Consequently this particular iterated direct-image unit is a right-derived model. -/
instance pushforwardLeray_isRightDerived :
    ((etaleDerivedPushforward (Of.ambientMap φ) :
      DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        (etaleDerivedPushforward Q.obj.right.hom :
          DerivedCategory (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))).IsRightDerivedFunctor
      (pushforwardLerayUnit X Λ φ)
      (HomologicalComplex.quasiIso
        (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)) := sorry

-- Local declaration justification (metaprogramming implementation): the compactification
-- triangle equality remains private while its equality transport is exposed.
set_option backward.privateInPublic true in
/-- The derived Leray isomorphism is obtained by uniqueness for the iterated direct-image unit, transported
along the specified underived composition iso and compactification triangle. -/
def pushforwardLerayIso :
    (etaleDerivedPushforward (Of.ambientMap φ) :
      DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        (etaleDerivedPushforward Q.obj.right.hom :
          DerivedCategory (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ≅
      etaleDerivedPushforward P.obj.right.hom :=
  RightDerived.natIsoOfIso
    (RF' := RightDerived.Cochain.functor (etaleModulePushforward P.obj.right.hom Λ))
    (DerivedCategory.Q :
      CochainComplex (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (HomologicalComplex.quasiIso
      (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (pushforwardLerayUnit X Λ φ)
    (RightDerived.Cochain.unit (etaleModulePushforward P.obj.right.hom Λ))
    (isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (etaleModulePushforwardCompIso (Of.ambientMap φ) Q.obj.right.hom ≪≫
          eqToIso (congrArg (fun f ↦ etaleModulePushforward f Λ)
            (ambientMap_comp_structure φ))) (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))))

/-- Canonical compactification transition: first the derived interior comparison, then
derived Leray. Resolutions occur after extension by zero. -/
@[irreducible]
def isoOfHom :
    (etaleDerivedLowerShriek X Q :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⟶
      (etaleDerivedLowerShriek X P :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  whiskerRight (derivedInteriorComparison X Λ φ)
      (etaleDerivedPushforward Q.obj.right.hom) ≫
    (Functor.associator
      (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
      (etaleDerivedPushforward (Of.ambientMap φ))
      (etaleDerivedPushforward Q.obj.right.hom)).hom ≫
    whiskerLeft (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
      (pushforwardLerayIso X Λ φ).hom

/-- Component of `isoOfHom` at an object of `D(X_étale, Λ)`. -/
@[irreducible]
def isoOfHom_app (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    ((etaleDerivedLowerShriek X Q :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))).obj K) ⟶
      ((etaleDerivedLowerShriek X P :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))).obj K) :=
  (isoOfHom X Λ φ).app K

/-- The compactification transition component is evaluation of the canonical transformation. -/
theorem isoOfHom_app_eq
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    isoOfHom_app X Λ φ K = (isoOfHom X Λ φ).app K := by
  unfold isoOfHom_app
  rfl

/-- The transition is the specified derived interior map followed by Leray. -/
theorem isoOfHom_eq :
    isoOfHom X Λ φ =
      whiskerRight (derivedInteriorComparison X Λ φ)
          (etaleDerivedPushforward Q.obj.right.hom) ≫
        (Functor.associator
          (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
          (etaleDerivedPushforward (Of.ambientMap φ))
          (etaleDerivedPushforward Q.obj.right.hom)).hom ≫
        whiskerLeft (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
          (pushforwardLerayIso X Λ φ).hom := by
  unfold isoOfHom
  rfl

/-- The comparison attached to the identity morphism of a compactification is
the identity. -/
theorem isoOfHom_refl :
    isoOfHom X Λ (𝟙 P) =
      𝟙 (etaleDerivedLowerShriek X P :
          DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  sorry

/-- Canonical compactification transitions are invertible on bounded-below
objects with torsion cohomology. -/
theorem isoOfHom_isIso_of_isGE_isTorsion
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n] :
    IsIso (isoOfHom_app X Λ φ K) := sorry

/-- Canonical compactification transitions are invertible for torsion coefficient rings. -/
theorem isoOfHom_isIso_of_isTorsion (hΛ : AddMonoid.IsTorsion Λ) :
    IsIso (isoOfHom X Λ φ) := sorry

/-- The canonical transition component is invertible on an admissible object. -/
instance isoOfHom_app_isIso
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    [Fact (Derived.compactSupportAdmissible X.left Λ K)] :
    IsIso ((isoOfHom X Λ φ).app K) := sorry

/-- The canonical transition is invertible after restriction to admissible objects. -/
instance isoOfHom_admissible_isIso :
    IsIso (whiskerLeft (Derived.compactSupportAdmissible X.left Λ).ι
      (isoOfHom X Λ φ)) := sorry

/-- A torsion coefficient ring makes every canonical compactification transition invertible. -/
instance isoOfHom_isIso [hΛ : Fact (AddMonoid.IsTorsion Λ)] :
    IsIso (isoOfHom X Λ φ) :=
  isoOfHom_isIso_of_isTorsion X Λ φ hΛ.out

variable {R : Of Y X} (ψ : Q ⟶ R)
variable [HasSheafify R.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : R.obj.right.left.Etale,
  HasWeakSheafify (R.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf R.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι R)).op.HasLeftKanExtension F]
variable [HasSheafCompose R.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify R.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [R.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι R)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι R)).op]
variable [(etaleExtensionByZero (Of.ι R) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι R) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι R) (ModuleCat.{u} Λ))]

/-- Comparisons along morphisms of compactifications reverse composition. -/
theorem isoOfHom_comp :
    isoOfHom X Λ (φ ≫ ψ) =
      (isoOfHom X Λ ψ ≫ isoOfHom X Λ φ :
        (etaleDerivedLowerShriek X R :
            DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⟶
          (etaleDerivedLowerShriek X P :
            DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))) :=
  sorry

/-- Parallel compactification morphisms induce equal transitions on admissible objects. -/
theorem isoOfHom_eq_of_parallel (χ : P ⟶ Q) :
    whiskerLeft (Derived.compactSupportAdmissible X.left Λ).ι (isoOfHom X Λ φ) =
      whiskerLeft (Derived.compactSupportAdmissible X.left Λ).ι (isoOfHom X Λ χ) := sorry

/-- Compactification models are naturally isomorphic over a torsion coefficient ring. -/
theorem independent [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (hΛ : AddMonoid.IsTorsion Λ) :
    IsIsomorphic
      (etaleDerivedLowerShriek X P :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
      (etaleDerivedLowerShriek X Q :
        DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) := sorry

/-- Compactification models restricted to admissible objects are naturally isomorphic. -/
theorem independent_admissible [CompactSpace X.left] [QuasiSeparatedSpace X.left] :
    IsIsomorphic
      ((Derived.compactSupportAdmissible X.left Λ).ι ⋙ etaleDerivedLowerShriek X P)
      ((Derived.compactSupportAdmissible X.left Λ).ι ⋙ etaleDerivedLowerShriek X Q) := sorry

/-- Compactification models agree up to isomorphism on bounded-below torsion objects. -/
theorem independent_obj [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n] :
    IsIsomorphic ((etaleDerivedLowerShriek X P).obj K)
      ((etaleDerivedLowerShriek X Q).obj K) := sorry

end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale

end
