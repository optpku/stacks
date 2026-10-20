module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation.InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image of relative differentials

This file gives the site-generic comparison between inverse image and relative
differentials.  Its input is a continuous functor of sites; the commutative-ring
sheafification adjunction supplies the structure map used by module pullback.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open scoped RelativeDerivation

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.RelativeDifferentials

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify K CommRingCat.{max u v}]
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- The section function underlying the pulled universal derivation. -/
noncomputable def comparisonSection (phi : O₁ ⟶ O₂) {U : Cᵒᵖ}
    (x : O₂.obj.obj U) :
    ((SheafOfModules.pushforward
      (InverseImage.structureMap (J := J) (K := K) F O₂)).obj
      (relativeDifferentials
        ((InverseImage.ringPullback (J := J) (K := K) F).map phi))).val.obj U :=
  (relativeDifferential
    ((InverseImage.ringPullback (J := J) (K := K) F).map phi)).d
    (((F.sheafAdjunctionContinuous CommRingCat.{max u v} J K).unit.app O₂).hom.app U x)

/-- The pulled universal differential is additive on sections. -/
theorem comparisonSection_add (phi : O₁ ⟶ O₂) {U : Cᵒᵖ}
    (x y : O₂.obj.obj U) :
    comparisonSection (J := J) (K := K) F phi (x + y) =
      comparisonSection (J := J) (K := K) F phi x +
        comparisonSection (J := J) (K := K) F phi y :=
  SheafOfModules.RelativeDerivation.InverseImage.pushforwardSection_add
    (J := J) (K := K) F phi
      (relativeDifferential
        ((InverseImage.ringPullback (J := J) (K := K) F).map phi)) x y

/-- The pulled universal differential satisfies the Leibniz rule. -/
theorem comparisonSection_mul (phi : O₁ ⟶ O₂) {U : Cᵒᵖ}
    (x y : O₂.obj.obj U) :
    comparisonSection (J := J) (K := K) F phi (x * y) =
      x • comparisonSection (J := J) (K := K) F phi y +
        y • comparisonSection (J := J) (K := K) F phi x :=
  SheafOfModules.RelativeDerivation.InverseImage.pushforwardSection_mul
    (J := J) (K := K) F phi
      (relativeDifferential
        ((InverseImage.ringPullback (J := J) (K := K) F).map phi)) x y

/-- The pulled universal differential is natural in the site object. -/
theorem comparisonSection_naturality (phi : O₁ ⟶ O₂)
    {U V : Cᵒᵖ} (rho : U ⟶ V) (x : O₂.obj.obj U) :
    comparisonSection (J := J) (K := K) F phi (O₂.obj.map rho x) =
      (((SheafOfModules.pushforward
        (InverseImage.structureMap (J := J) (K := K) F O₂)).obj
        (relativeDifferentials
          ((InverseImage.ringPullback (J := J) (K := K) F).map phi))).val.map rho)
          (comparisonSection (J := J) (K := K) F phi x) :=
  SheafOfModules.RelativeDerivation.InverseImage.pushforwardSection_naturality
    (J := J) (K := K) F phi
      (relativeDifferential
        ((InverseImage.ringPullback (J := J) (K := K) F).map phi)) rho x

/-- The pulled universal differential vanishes on the base ring sheaf. -/
theorem comparisonSection_base (phi : O₁ ⟶ O₂) {U : Cᵒᵖ}
    (x : O₁.obj.obj U) :
    comparisonSection (J := J) (K := K) F phi (phi.hom.app U x) = 0 :=
  SheafOfModules.RelativeDerivation.InverseImage.pushforwardSection_base
    (J := J) (K := K) F phi
      (relativeDifferential
        ((InverseImage.ringPullback (J := J) (K := K) F).map phi)) x

/-- The relative derivation obtained by applying inverse image to the universal
differential. -/
@[stacks 08RR "inverse-image differential derivation",
  stacks 08TQ "inverse-image differential derivation"]
noncomputable def comparisonDerivation (phi : O₁ ⟶ O₂) :
    Der[phi ; (SheafOfModules.pushforward
      (InverseImage.structureMap (J := J) (K := K) F O₂)).obj
      (relativeDifferentials
        ((InverseImage.ringPullback (J := J) (K := K) F).map phi))] :=
  SheafOfModules.RelativeDerivation.InverseImage.pushforward
    (J := J) (K := K) F phi
      (relativeDifferential
        ((InverseImage.ringPullback (J := J) (K := K) F).map phi))

variable [(SheafOfModules.pushforward
  (InverseImage.structureMap (J := J) (K := K) F O₂)).IsRightAdjoint]

/-- The canonical comparison from the inverse image of relative differentials
to the relative differentials of the inverse-image ring map. -/
@[stacks 08RR "inverse-image differential comparison",
  stacks 08TQ "inverse-image differential comparison"]
noncomputable def comparison (phi : O₁ ⟶ O₂) :
    (InverseImage.modulePullback (J := J) (K := K) F O₂).obj
      (relativeDifferentials phi) ⟶
      relativeDifferentials
        ((InverseImage.ringPullback (J := J) (K := K) F).map phi) :=
  (comparisonDerivation (J := J) (K := K) F phi).pullbackDesc

/-- The inverse-image comparison is characterized by the pulled universal derivation. -/
@[stacks 08RR "inverse-image differential comparison specification",
  stacks 08TQ "inverse-image differential comparison specification"]
theorem comparison_spec (phi : O₁ ⟶ O₂) :
    SheafOfModules.RelativeDerivation.IsPullbackDesc
      (comparisonDerivation (J := J) (K := K) F phi)
      (comparison (J := J) (K := K) F phi) :=
  SheafOfModules.RelativeDerivation.pullbackDesc_isPullbackDesc
    (comparisonDerivation (J := J) (K := K) F phi)

/-- A morphism compatible with the pulled universal derivation is the canonical inverse-image
comparison. -/
@[stacks 08RR "inverse-image differential comparison uniqueness",
  stacks 08TQ "inverse-image differential comparison uniqueness"]
theorem eq_comparison (phi : O₁ ⟶ O₂)
    {tau :
      (InverseImage.modulePullback (J := J) (K := K) F O₂).obj
          (relativeDifferentials phi) ⟶
        relativeDifferentials
          ((InverseImage.ringPullback (J := J) (K := K) F).map phi)}
    (h_tau :
      SheafOfModules.RelativeDerivation.IsPullbackDesc
        (comparisonDerivation (J := J) (K := K) F phi) tau) :
    tau = comparison (J := J) (K := K) F phi :=
  SheafOfModules.RelativeDerivation.eq_pullbackDesc
    (comparisonDerivation (J := J) (K := K) F phi) h_tau

/-- The universal relative derivation followed by the unit of the module
pullback-pushforward adjunction. -/
noncomputable def unitDerivation (phi : O₁ ⟶ O₂) :
    Der[phi ; (SheafOfModules.pushforward
      (InverseImage.structureMap (J := J) (K := K) F O₂)).obj
      ((InverseImage.modulePullback (J := J) (K := K) F O₂).obj
        (relativeDifferentials phi))] :=
  (relativeDifferential phi).postcomp
    ((SheafOfModules.pullbackPushforwardAdjunction
      (InverseImage.structureMap (J := J) (K := K) F O₂)).unit.app
        (relativeDifferentials phi)).val

/-- Transporting the adjunction-unit derivation back along inverse image gives
a derivation of the pulled-back ring map. -/
noncomputable def inverseDerivation (phi : O₁ ⟶ O₂) :
    Der[(InverseImage.ringPullback (J := J) (K := K) F).map phi ;
      (InverseImage.modulePullback (J := J) (K := K) F O₂).obj
        (relativeDifferentials phi)] :=
  (SheafOfModules.RelativeDerivation.InverseImage.equiv
    (J := J) (K := K) F phi).symm
      (unitDerivation (J := J) (K := K) F phi)

/-- The morphism inverse to the canonical inverse-image comparison on relative differentials. -/
@[stacks 08TQ "inverse-image relative-differentials comparison inverse"]
noncomputable def comparisonInv (phi : O₁ ⟶ O₂) :
    relativeDifferentials
        ((InverseImage.ringPullback (J := J) (K := K) F).map phi) ⟶
      (InverseImage.modulePullback (J := J) (K := K) F O₂).obj
        (relativeDifferentials phi) :=
  relativeDifferentialDesc
    ((InverseImage.ringPullback (J := J) (K := K) F).map phi)
    (inverseDerivation (J := J) (K := K) F phi)

/-- The inverse-image relative-differentials comparison followed by its named inverse is the
identity. -/
@[simp, stacks 08TQ "inverse-image relative-differentials forward-inverse law"]
theorem comparison_hom_inv_id (phi : O₁ ⟶ O₂) :
    comparison (J := J) (K := K) F phi ≫
        comparisonInv (J := J) (K := K) F phi = 𝟙 _ := sorry

/-- The named inverse followed by the inverse-image relative-differentials comparison is the
identity. -/
@[simp, stacks 08TQ "inverse-image relative-differentials inverse-forward law"]
theorem comparison_inv_hom_id (phi : O₁ ⟶ O₂) :
    comparisonInv (J := J) (K := K) F phi ≫
        comparison (J := J) (K := K) F phi = 𝟙 _ := sorry

/-- The inverse-image comparison on relative differentials as explicit Iso data. -/
@[stacks 08TQ "inverse-image comparison isomorphism"]
noncomputable def comparisonIso (phi : O₁ ⟶ O₂) :
    (InverseImage.modulePullback (J := J) (K := K) F O₂).obj
        (relativeDifferentials phi) ≅
      relativeDifferentials
        ((InverseImage.ringPullback (J := J) (K := K) F).map phi) where
  hom := comparison (J := J) (K := K) F phi
  inv := comparisonInv (J := J) (K := K) F phi
  hom_inv_id := comparison_hom_inv_id (J := J) (K := K) F phi
  inv_hom_id := comparison_inv_hom_id (J := J) (K := K) F phi

/-- The canonical inverse-image comparison on relative differentials is an
isomorphism. -/
@[stacks 08TQ]
instance comparison_isIso (phi : O₁ ⟶ O₂) :
    IsIso (comparison (J := J) (K := K) F phi) :=
  (comparisonIso (J := J) (K := K) F phi).isIso_hom

/-- The forward map of the inverse-image comparison isomorphism is the canonical comparison. -/
@[stacks 08TQ "inverse-image comparison isomorphism hom", simp]
theorem comparisonIso_hom (phi : O₁ ⟶ O₂) :
    (comparisonIso (J := J) (K := K) F phi).hom =
      comparison (J := J) (K := K) F phi := rfl

/-- The inverse projection of the canonical inverse-image isomorphism is the
explicit comparison inverse. -/
@[stacks 08TQ "inverse-image comparison isomorphism inverse", simp]
theorem comparisonIso_inv (phi : O₁ ⟶ O₂) :
    (comparisonIso (J := J) (K := K) F phi).inv =
      comparisonInv (J := J) (K := K) F phi := rfl

end SheafOfModules.RingedSite.RelativeDifferentials
