/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Elements of the quotient ideal map into the kernel ideal that defines the conormal sheaf
of the affine quotient morphism. -/
theorem quotientMapIdeal_le_conormalIdeal :
    I ≤ (conormalIdeal
      (RingedSpace.Hom.inverseImageStructureSheafHomComm
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toShHom)
      (Opposite.op ⊤)).comap
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base).unit.app
              (Spec (CommRingCat.of R)).sheaf).hom.app (Opposite.op ⊤))).hom) := sorry

set_option maxHeartbeats 4000000 in
/-- The canonical map from `I / I²` to the global sections of the conormal sheaf of
`Spec (R ⧸ I) ⟶ Spec R`. -/
noncomputable def quotientMapCotangentToSections :
    ModuleCat.of (R ⧸ I) I.Cotangent ⟶
      (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I))).obj
        (Scheme.Hom.conormalSheaf
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let α := RingedSpace.Hom.inverseImageStructureSheafHomComm q.toShHom
  let W : (Opens (Spec (CommRingCat.of R)))ᵒᵖ := Opposite.op ⊤
  let V : (Opens (Spec (CommRingCat.of (R ⧸ I))))ᵒᵖ := Opposite.op ⊤
  let F : CommRingCat.of R ⟶
      ((TopCat.Sheaf.pullback CommRingCat.{u} q.toShHom.hom.base).obj
        (Spec (CommRingCat.of R)).sheaf).obj.obj V :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (((TopCat.Sheaf.pullbackPushforwardAdjunction
        CommRingCat.{u} q.toShHom.hom.base).unit.app
        (Spec (CommRingCat.of R)).sheaf).hom.app W)
  let G : CommRingCat.of (R ⧸ I) ⟶
      (Spec (CommRingCat.of (R ⧸ I))).sheaf.obj.obj V :=
    (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).inv
  let J := conormalIdeal α V
  let η := (conormalSourcePresheafUnit α).app V
  let source : ModuleCat (R ⧸ I) := ModuleCat.of (R ⧸ I) I.Cotangent
  let target : ModuleCat (R ⧸ I) :=
    (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I))).obj
      (Scheme.Hom.conormalSheaf q)
  let targetR : ModuleCat R :=
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj target
  have hF (r : R) : α.hom.app V (F r) = G (Ideal.Quotient.mk I r) := by
    have hs :
        (TopCat.Sheaf.pullbackPushforwardAdjunction
              CommRingCat.{u} q.toShHom.hom.base).unit.app
              (Spec (CommRingCat.of R)).sheaf ≫
            (TopCat.Sheaf.pushforward CommRingCat.{u} q.toShHom.hom.base).map α =
          RingedSpace.Hom.commRingSheafPushforwardMap q.toShHom := by
      simpa only [Functor.id_obj, Adjunction.homEquiv_unit,
        RingedSpace.Hom.inverseImageStructureSheafHomComm, α] using
        (Equiv.apply_symm_apply
          ((TopCat.Sheaf.pullbackPushforwardAdjunction
            CommRingCat.{u} q.toShHom.hom.base).homEquiv
            (Spec (CommRingCat.of R)).sheaf
            (Spec (CommRingCat.of (R ⧸ I))).sheaf)
          (RingedSpace.Hom.commRingSheafPushforwardMap q.toShHom))
    have hsW := congrArg (fun f ↦ f.hom.app W) hs
    change
      (((TopCat.Sheaf.pullbackPushforwardAdjunction
        CommRingCat.{u} q.toShHom.hom.base).unit.app
        (Spec (CommRingCat.of R)).sheaf).hom.app W) ≫ α.hom.app V = q.appTop at hsW
    have hsF : F ≫ α.hom.app V =
        CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ G := by
      dsimp only [F, G]
      rw [Category.assoc, hsW]
      exact
        (Scheme.ΓSpecIso_inv_naturality
          (CommRingCat.ofHom (Ideal.Quotient.mk I))).symm
    exact ConcreteCategory.congr_hom hsF r
  let conormalNative := (conormalPresheaf α).obj V
  let sectionsNative :=
    ((restrictionAlong α).obj
      (conormalSource
        (J := Opens.grothendieckTopology (Spec (CommRingCat.of (R ⧸ I))))
        (O₂ := (TopCat.Sheaf.pullback CommRingCat.{u} q.toShHom.hom.base).obj
          (Spec (CommRingCat.of R)).sheaf)
        (O₃ := (Spec (CommRingCat.of (R ⧸ I))).sheaf) α)).val.obj V
  let conormalR : ModuleCat R :=
    (ModuleCat.restrictScalars F.hom).obj conormalNative
  let sectionsR : ModuleCat R :=
    (ModuleCat.restrictScalars F.hom).obj sectionsNative
  let ηR : conormalR ⟶ sectionsR := (ModuleCat.restrictScalars F.hom).map η
  let sectionsToTarget : sectionsR ⟶ targetR :=
    ModuleCat.homMk (𝟙 _) (fun r ↦ by
      have hr : target.smul (Ideal.Quotient.mk I r) =
          sectionsNative.smul (F.hom r) := by
        change ((conormalSource α).val.obj V).smul
            (G.hom (Ideal.Quotient.mk I r)) =
          ((conormalSource α).val.obj V).smul (α.hom.app V (F.hom r))
        rw [hF]
      rw [Category.id_comp, Category.comp_id]
      change target.smul (Ideal.Quotient.mk I r) =
        sectionsNative.smul (F.hom r)
      exact hr)
  let idealToJ : I →+ J := {
    toFun x :=
      ⟨F.hom x, quotientMapIdeal_le_conormalIdeal I x.2⟩
    map_zero' := by
      ext
      exact map_zero F.hom
    map_add' x y := by
      ext
      simpa only [Submodule.coe_add] using map_add F.hom (x : R) (y : R) }
  let idealGenerator : ModuleCat.of R I ⟶ conormalR :=
    ModuleCat.homMk
      (AddCommGrpCat.ofHom (J.toCotangent.toAddMonoidHom.comp idealToJ))
      (fun r ↦ by
        ext x
        change (conormalR.smul r).hom (J.toCotangent (idealToJ x)) =
          J.toCotangent
            (idealToJ (((ModuleCat.of R I).smul r).hom x))
        have hx : idealToJ (((ModuleCat.of R I).smul r).hom x) =
            F.hom r • idealToJ x := by
          change idealToJ (r • (show I from x)) = F.hom r • idealToJ x
          apply Subtype.ext
          change F.hom (r * ((show I from x) : R)) =
            F.hom r * F.hom ((show I from x) : R)
          exact map_mul F.hom r ((show I from x) : R)
        rw [hx, map_smul]
        change (conormalR.smul r).hom (J.toCotangent (idealToJ x)) =
          (conormalNative.smul (F.hom r)).hom (J.toCotangent (idealToJ x))
        rfl)
  let generator : I →ₗ[R] targetR :=
    (idealGenerator ≫ ηR ≫ sectionsToTarget).hom
  let liftedR : I.Cotangent →ₗ[R] targetR :=
    Ideal.Cotangent.lift generator (fun x y ↦ by
      change sectionsToTarget.hom (ηR.hom (J.toCotangent
        ⟨F.hom (x * y), quotientMapIdeal_le_conormalIdeal I (x * y).2⟩)) = 0
      have hz : J.toCotangent
          ⟨F.hom (x * y), quotientMapIdeal_le_conormalIdeal I (x * y).2⟩ = 0 := by
        apply (Ideal.toCotangent_eq_zero J _).2
        change F.hom (x * y) ∈ J ^ 2
        rw [map_mul, pow_two]
        exact Ideal.mul_mem_mul
          (quotientMapIdeal_le_conormalIdeal I x.2)
          (quotientMapIdeal_le_conormalIdeal I y.2)
      rw [hz, map_zero, map_zero])
  exact ModuleCat.homMk (AddCommGrpCat.ofHom liftedR.toAddMonoidHom) (fun s ↦ by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    ext x
    change (target.smul (Ideal.Quotient.mk I r)).hom (liftedR x) =
      liftedR ((source.smul (Ideal.Quotient.mk I r)).hom x)
    exact (liftedR.map_smul r x).symm)

/-- On a cotangent generator, the affine comparison applies the canonical map from the ideal
to the sectionwise conormal ideal and then the conormal sheafification unit. -/
theorem quotientMapCotangentToSections_toCotangent (x : I) :
    let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    let α := RingedSpace.Hom.inverseImageStructureSheafHomComm q.toShHom
    let W : (Opens (Spec (CommRingCat.of R)))ᵒᵖ := Opposite.op ⊤
    let V : (Opens (Spec (CommRingCat.of (R ⧸ I))))ᵒᵖ := Opposite.op ⊤
    let F : CommRingCat.of R ⟶
        ((TopCat.Sheaf.pullback CommRingCat.{u} q.toShHom.hom.base).obj
          (Spec (CommRingCat.of R)).sheaf).obj.obj V :=
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (((TopCat.Sheaf.pullbackPushforwardAdjunction
          CommRingCat.{u} q.toShHom.hom.base).unit.app
          (Spec (CommRingCat.of R)).sheaf).hom.app W)
    quotientMapCotangentToSections I (I.toCotangent x) =
      (conormalSourcePresheafUnit α).app V
        ((conormalIdeal α V).toCotangent
          ⟨F.hom x, quotientMapIdeal_le_conormalIdeal I x.2⟩) := sorry

/-- The canonical affine comparison identifies `I / I²` with the global sections of the
conormal sheaf of `Spec (R ⧸ I) ⟶ Spec R`. -/
theorem quotientMapCotangentToSections_isIso :
    IsIso (quotientMapCotangentToSections I) := sorry

end AlgebraicGeometry.Scheme.Hom.Conormal
