/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.QuasiCoherent
import StacksCheckRecall

/-!
# Lemma 27.2.2 compatibility entry point

The reusable basis-indexed quasi-coherent-module gluing datum and its
realization and uniqueness APIs are owned by
`ReasLib.AlgebraicGeometry.Scheme.Gluing.Basis.QuasiCoherent`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- The scheme-valued part of the datum is the existing basis gluing structure. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.{u, v} :
    Scheme.{u} → Type (max (u + 1) (v + 1)))

/- The scheme gluing owner supplies equipped realizations. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization :
    ∀ {S : Scheme.{u}} (scheme : Scheme.BasisSchemeGluing.{u, v} S),
      Type (max (u + 1) v))

/- The scheme gluing owner supplies linked isomorphisms between equipped realizations. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.RealizationIso :
    ∀ {S : Scheme.{u}} (scheme : Scheme.BasisSchemeGluing.{u, v} S)
      (R R' : Scheme.BasisSchemeGluing.Realization scheme),
      Type (max u v))

/- The existing scheme gluing theorem supplies a realization. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization.nonempty :
    ∀ {S : Scheme.{u}} (scheme : Scheme.BasisSchemeGluing.{u, v} S),
      Nonempty (Scheme.BasisSchemeGluing.Realization scheme))

/- The existing scheme gluing theorem supplies the unique linked realization isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.BasisSchemeGluing.Realization.existsUniqueIso :
    ∀ {S : Scheme.{u}} (scheme : Scheme.BasisSchemeGluing.{u, v} S)
      (R R' : Scheme.BasisSchemeGluing.Realization scheme),
      ∃ e : Scheme.BasisSchemeGluing.RealizationIso scheme R R',
        ∀ e' : Scheme.BasisSchemeGluing.RealizationIso scheme R R', e' = e)

/- Equation 27.2.2.1 uses the shared relative gluing comparison morphism. -/
#check
  (AlgebraicGeometry.Scheme.Modules.relativeGlueingComparison :
    ∀ {S X X_U X_V : Scheme.{u}} {V : S.Opens} (f : X ⟶ S) (ρ : X_V ⟶ X_U)
      (M_U : X_U.Modules) (M_V : X_V.Modules) (M : X.Modules)
      (i_V : (f ⁻¹ᵁ V).toScheme ≅ X_V) {U : S.Opens} (hVU : V ≤ U)
      (i_U : (f ⁻¹ᵁ U).toScheme ≅ X_U)
      (sourceIdentification :
        (Scheme.Modules.pullback ρ).obj M_U ≅
          (Scheme.Modules.pullback i_V.inv).obj
            (((Scheme.Modules.pullback i_U.hom).obj M_U).restrict
              (X.homOfLE (f.preimage_mono hVU))))
      (thetaURestrict :
        (Scheme.Modules.pullback i_V.inv).obj
            (((Scheme.Modules.pullback i_U.hom).obj M_U).restrict
              (X.homOfLE (f.preimage_mono hVU))) ⟶
          (Scheme.Modules.pullback i_V.inv).obj (M.restrict (f ⁻¹ᵁ V).ι))
      (thetaV :
        M_V ≅ (Scheme.Modules.pullback i_V.inv).obj (M.restrict (f ⁻¹ᵁ V).ι)),
      (Scheme.Modules.pullback ρ).obj M_U ⟶ M_V)

/- The shared comparison theorem records the complete three-factor formula. -/
#check
  (AlgebraicGeometry.Scheme.Modules.relativeGlueingComparison_def :
    ∀ {S X X_U X_V : Scheme.{u}} {V : S.Opens} (f : X ⟶ S) (ρ : X_V ⟶ X_U)
      (M_U : X_U.Modules) (M_V : X_V.Modules) (M : X.Modules)
      (i_V : (f ⁻¹ᵁ V).toScheme ≅ X_V) {U : S.Opens} (hVU : V ≤ U)
      (i_U : (f ⁻¹ᵁ U).toScheme ≅ X_U)
      (sourceIdentification :
        (Scheme.Modules.pullback ρ).obj M_U ≅
          (Scheme.Modules.pullback i_V.inv).obj
            (((Scheme.Modules.pullback i_U.hom).obj M_U).restrict
              (X.homOfLE (f.preimage_mono hVU))))
      (thetaURestrict :
        (Scheme.Modules.pullback i_V.inv).obj
            (((Scheme.Modules.pullback i_U.hom).obj M_U).restrict
              (X.homOfLE (f.preimage_mono hVU))) ⟶
          (Scheme.Modules.pullback i_V.inv).obj (M.restrict (f ⁻¹ᵁ V).ι))
      (thetaV :
        M_V ≅ (Scheme.Modules.pullback i_V.inv).obj (M.restrict (f ⁻¹ᵁ V).ι)),
      Scheme.Modules.relativeGlueingComparison f ρ M_U M_V M i_V hVU i_U
          sourceIdentification thetaURestrict thetaV =
        sourceIdentification.hom ≫ thetaURestrict ≫ thetaV.inv)

/- The shared datum retains the complete basis-indexed scheme and quasi-coherent-module gluing
data. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.{u, v} :
    Scheme.{u} → Type (max (u + 1) (v + 1)))

/- The explicit companion constructor extends scheme gluing data by exactly the module fields. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.ofBasisSchemeGluing :
    ∀ {S : Scheme.{u}} (scheme : Scheme.BasisSchemeGluing.{u, v} S)
      (F : ∀ i : scheme.ι, (scheme.X i).Modules)
      (isQuasiCoherent : ∀ i : scheme.ι, (F i).IsQuasicoherent)
      (theta : ∀ ⦃i j : scheme.ι⦄ (hij : scheme.U i ≤ scheme.U j),
        (Scheme.Modules.pullback (scheme.rho hij)).obj (F j) ≅ F i)
      (theta_cocycle : ∀ ⦃i j k : scheme.ι⦄ (hij : scheme.U i ≤ scheme.U j)
        (hjk : scheme.U j ≤ scheme.U k),
        ((Scheme.Modules.pullbackCongr (scheme.cocycle hij hjk)).hom.app (F k)) ≫
              ((Scheme.Modules.pullbackComp (scheme.rho hij) (scheme.rho hjk)).inv.app (F k)) ≫
            (Scheme.Modules.pullback (scheme.rho hij)).map (theta hjk).hom ≫
          (theta hij).hom =
            (theta (hij.trans hjk)).hom),
      Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)

/- The local module identification has the required inverse-coordinate orientation. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.reorientedLocalModuleIso :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      {Y : Scheme.{u}} (toBase : Y ⟶ S) (M : Y.Modules)
      (localSchemeIso : ∀ i : D.ι, (toBase ⁻¹ᵁ D.U i).toScheme ≅ D.X i)
      (localModuleIso : ∀ i : D.ι,
        (Scheme.Modules.pullback (localSchemeIso i).hom).obj (D.F i) ≅
          M.restrict (toBase ⁻¹ᵁ D.U i).ι)
      (i : D.ι),
      D.F i ≅ (Scheme.Modules.pullback (localSchemeIso i).inv).obj
        (M.restrict (toBase ⁻¹ᵁ D.U i).ι))

/- The recorded local transition determines the source identification in 27.2.2.1. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.localTransitionSourceIso :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      {Y : Scheme.{u}} (toBase : Y ⟶ S)
      (localSchemeIso : ∀ i : D.ι, (toBase ⁻¹ᵁ D.U i).toScheme ≅ D.X i)
      {i j : D.ι} (hij : D.U i ≤ D.U j)
      (localTransition :
        (localSchemeIso i).inv ≫ Y.homOfLE (toBase.preimage_mono hij) ≫
          (localSchemeIso j).hom = D.rho hij),
      (Scheme.Modules.pullback (D.rho hij)).obj (D.F j) ≅
        (Scheme.Modules.pullback (localSchemeIso i).inv).obj
          (((Scheme.Modules.pullback (localSchemeIso j).hom).obj (D.F j)).restrict
            (Y.homOfLE (toBase.preimage_mono hij))))

/- Restricting the larger local module identification gives the second comparison factor. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.restrictedLocalModuleIso :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      {Y : Scheme.{u}} (toBase : Y ⟶ S) (M : Y.Modules)
      (localSchemeIso : ∀ i : D.ι, (toBase ⁻¹ᵁ D.U i).toScheme ≅ D.X i)
      (localModuleIso : ∀ i : D.ι,
        (Scheme.Modules.pullback (localSchemeIso i).hom).obj (D.F i) ≅
          M.restrict (toBase ⁻¹ᵁ D.U i).ι)
      {i j : D.ι} (hij : D.U i ≤ D.U j),
      (Scheme.Modules.pullback (localSchemeIso i).inv).obj
          (((Scheme.Modules.pullback (localSchemeIso j).hom).obj (D.F j)).restrict
            (Y.homOfLE (toBase.preimage_mono hij))) ≅
        (Scheme.Modules.pullback (localSchemeIso i).inv).obj
          (M.restrict (toBase ⁻¹ᵁ D.U i).ι))

/- Local compatibility is the complete transition equation for all nested basis opens. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.LocalModuleCompatibility :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      {Y : Scheme.{u}} (toBase : Y ⟶ S) (M : Y.Modules)
      (localSchemeIso : ∀ i : D.ι, (toBase ⁻¹ᵁ D.U i).toScheme ≅ D.X i)
      (localTransition : ∀ ⦃i j : D.ι⦄ (hij : D.U i ≤ D.U j),
        (localSchemeIso i).inv ≫ Y.homOfLE (toBase.preimage_mono hij) ≫
          (localSchemeIso j).hom = D.rho hij)
      (localModuleIso : ∀ i : D.ι,
        (Scheme.Modules.pullback (localSchemeIso i).hom).obj (D.F i) ≅
          M.restrict (toBase ⁻¹ᵁ D.U i).ι),
      Prop)

/- The shared producer surface is the explicit equipped module realization. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.Realization :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S),
      Type (max (u + 1) v))

/- Forgetting module data gives the existing equipped scheme realization. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.Realization.toSchemeRealization :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (R : Scheme.Modules.BasisQuasiCoherentGluing.Realization D),
      D.toBasisSchemeGluing.Realization)

/- A realization exposes its local module identification in inverse coordinates. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.Realization.inverseLocalModuleIso :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (R : Scheme.Modules.BasisQuasiCoherentGluing.Realization D) (i : D.ι),
      D.F i ≅ (Scheme.Modules.pullback (R.localSchemeIso i).inv).obj
        (R.M.restrict (R.toBase ⁻¹ᵁ D.U i).ι))

/- Compatible equipped realizations are related by the linked realization-isomorphism data. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.RealizationIso :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (R R' : Scheme.Modules.BasisQuasiCoherentGluing.Realization D),
      Type (max u v))

/- The global comparison is explicit isomorphism data for a scheme-module pair over the base. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.GlobalPairOverIso :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
      (g : Y ⟶ S) (N : Y.Modules),
      Type u)

/- The linked global comparisons determine the local module comparison without choice. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.inducedLocalModuleComparison :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (R R' : Scheme.Modules.BasisQuasiCoherentGluing.Realization D)
      (schemeIso : D.toBasisSchemeGluing.RealizationIso
        (Scheme.Modules.BasisQuasiCoherentGluing.Realization.toSchemeRealization D R)
        (Scheme.Modules.BasisQuasiCoherentGluing.Realization.toSchemeRealization D R'))
      (moduleIso : (Scheme.Modules.pullback schemeIso.iso.hom).obj R'.M ≅ R.M)
      (i : D.ι),
      (Scheme.Modules.pullback (R'.localSchemeIso i).inv).obj
          (R'.M.restrict (R'.toBase ⁻¹ᵁ D.U i).ι) ≅
        (Scheme.Modules.pullback (R.localSchemeIso i).inv).obj
          (R.M.restrict (R.toBase ⁻¹ᵁ D.U i).ι))

/- Forgetting local compatibility yields the underlying global pair isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.RealizationIso.globalPairOverIso :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      {R R' : Scheme.Modules.BasisQuasiCoherentGluing.Realization D}
      (e : Scheme.Modules.BasisQuasiCoherentGluing.RealizationIso D R R'),
      Scheme.Modules.BasisQuasiCoherentGluing.GlobalPairOverIso
        R.toBase R.M R'.toBase R'.M)

/- The consumer predicate retains the global pair together with all local realization data and
the transition compatibility. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.RealizesWithModule :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      {X : Scheme.{u}},
      (X ⟶ S) → X.Modules → Prop)

/- An equipped realization directly supplies the source-facing consumer predicate. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.Realization.realizesWithModule :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (R : Scheme.Modules.BasisQuasiCoherentGluing.Realization D),
      D.RealizesWithModule R.toBase R.M)

/- Lemma 27.2.2: compatible basis-indexed schemes and quasi-coherent modules have an equipped
global realization unique up to a unique compatible isomorphism. -/
@[stacks 01LI] #check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.existsRealizationUniqueUpToUniqueIso :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S),
      ∃ R : Scheme.Modules.BasisQuasiCoherentGluing.Realization D,
        ∀ R' : Scheme.Modules.BasisQuasiCoherentGluing.Realization D,
          ∃ e : Scheme.Modules.BasisQuasiCoherentGluing.RealizationIso D R R',
            ∀ e' : Scheme.Modules.BasisQuasiCoherentGluing.RealizationIso D R R', e' = e)

/- The compatible local data admit an equipped global realization. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.Realization.nonempty :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S),
      Nonempty (Scheme.Modules.BasisQuasiCoherentGluing.Realization D))

/- The equipped global realization is unique up to a unique isomorphism respecting its scheme
and module identifications. -/
#check
  (AlgebraicGeometry.Scheme.Modules.BasisQuasiCoherentGluing.Realization.existsUniqueIso :
    ∀ {S : Scheme.{u}} (D : Scheme.Modules.BasisQuasiCoherentGluing.{u, v} S)
      (R R' : Scheme.Modules.BasisQuasiCoherentGluing.Realization D),
      ∃ e : Scheme.Modules.BasisQuasiCoherentGluing.RealizationIso D R R',
        ∀ e' : Scheme.Modules.BasisQuasiCoherentGluing.RealizationIso D R R', e' = e)
