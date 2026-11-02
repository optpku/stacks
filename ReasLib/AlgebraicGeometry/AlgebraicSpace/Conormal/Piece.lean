/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ClosedImmersion

/-!
# Degree-n pieces of the conormal algebra of an immersion

For an immersion `i : Z ⟶ X` of algebraic spaces, the coborder closed
immersion `Z ⟶ X \ ∂Z` has kernel ideal `I`. The degree-`n` piece
`C_{Z/X, n}` is the pullback to `Z` of the successive quotient `I^n / I^{n+1}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/-- The coborder ideal power `I^n ⊂ 𝒪_{X \ ∂Z}` of the kernel ideal of
`liftCoborder i`. -/
noncomputable def coborderIdealPower (n : ℕ) : IdealSubobject (Hom.coborder i) :=
  Modules.idealPowerProductSubobject
    (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
    (SheafOfModules.unit (structureSheaf (Hom.coborder i))) n

/-- `coborderIdealPower i n` is the ideal-power product of the coborder kernel
ideal against the structure module. -/
theorem coborderIdealPower_eq (n : ℕ) :
    coborderIdealPower i n =
      Modules.idealPowerProductSubobject
        (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (SheafOfModules.unit (structureSheaf (Hom.coborder i))) n :=
  rfl

/-- In degree one, the coborder ideal power is the coborder kernel ideal. -/
theorem coborderIdealPower_one :
    coborderIdealPower i 1 =
      Hom.idealSheafSubobject (IsImmersion.liftCoborder i) :=
  by
    let I := Hom.idealSheafSubobject (IsImmersion.liftCoborder i)
    let O := SheafOfModules.unit (structureSheaf (Hom.coborder i))
    let T : Subobject O := ⊤
    let e := Modules.structureModuleIsoTensorUnit (Hom.coborder i)
    haveI : IsIso T.arrow := by dsimp [T]; infer_instance
    change imageSubobject (Modules.action I (T : (Hom.coborder i).Modules) ≫ T.arrow) = I
    have h : Modules.action I (T : (Hom.coborder i).Modules) ≫ T.arrow =
        ((I : (Hom.coborder i).Modules) ◁ (T.arrow ≫ e.hom)) ≫
          (ρ_ (I : (Hom.coborder i).Modules)).hom ≫ I.arrow := by
      apply (cancel_mono e.hom).1
      dsimp [Modules.action]
      simp only [Category.assoc]
      rw [← leftUnitor_naturality, ← comp_whiskerRight_assoc,
        ← whisker_exchange_assoc, unitors_equal, rightUnitor_naturality]
    simp only [h, ← Category.assoc]
    rw [imageSubobject_iso_comp, imageSubobject_mono, Subobject.mk_arrow]

/-- The successive coborder quotient `I^n / I^{n+1}` as an
`𝒪_{X \ ∂Z}`-module. -/
noncomputable def coborderQuotient (n : ℕ) : (Hom.coborder i).Modules :=
  Modules.quotientByIdeal
    (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
    (coborderIdealPower i n).toModule

/-- `coborderQuotient i n` is the quotient of `I^n` by the action of `I`. -/
theorem coborderQuotient_eq (n : ℕ) :
    coborderQuotient i n =
      Modules.quotientByIdeal
        (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (coborderIdealPower i n).toModule :=
  rfl

/-- The degree-`n` piece `C_{Z/X, n}` of the conormal algebra of an immersion,
as the pullback to `Z` of `I^n / I^{n+1}`. -/
noncomputable def piece (n : ℕ) : Z.Modules :=
  (Modules.pullback (IsImmersion.liftCoborder i)).obj (coborderQuotient i n)

/-- `piece i n` is the coborder pullback of `coborderQuotient i n`. -/
theorem piece_eq (n : ℕ) :
    piece i n =
      (Modules.pullback (IsImmersion.liftCoborder i)).obj (coborderQuotient i n) :=
  rfl

/-- The canonical comparison `I^n / I^{n+1} ⟶ (liftCoborder i)_* C_{Z/X, n}`
given by the module adjunction unit of the coborder closed immersion. -/
noncomputable def piecePushforwardComparison (n : ℕ) :
    coborderQuotient i n ⟶
      (Modules.pushforward (IsImmersion.liftCoborder i)).obj (piece i n) :=
  (Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).unit.app
    (coborderQuotient i n)

/-- `piecePushforwardComparison i n` is the coborder adjunction unit at
`coborderQuotient i n`. -/
theorem piecePushforwardComparison_eq (n : ℕ) :
    piecePushforwardComparison i n =
      (Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).unit.app
        (coborderQuotient i n) :=
  rfl

/-- The degree-`n` conormal piece is the coborder pullback of `I^n / I^{n+1}`
along the coborder closed immersion. -/
theorem piece_spec (n : ℕ) :
    piece i n =
        (Modules.pullback (IsImmersion.liftCoborder i)).obj (coborderQuotient i n) ∧
      coborderQuotient i n =
        Modules.quotientByIdeal
          (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
          (coborderIdealPower i n).toModule ∧
      IsClosedImmersion (IsImmersion.liftCoborder i) :=
  ⟨rfl, rfl, inferInstance⟩

/-- The successive coborder quotient `I^n / I^{n+1}` is quasi-coherent. -/
instance instIsQuasicoherent_coborderQuotient (n : ℕ) :
    (coborderQuotient i n).IsQuasicoherent :=
  by
    let Y := Hom.coborder i
    let I := Hom.idealSheafSubobject (IsImmersion.liftCoborder i)
    haveI : I.toModule.IsQuasicoherent :=
      (inferInstance : IsQuasiCoherent I).quasiCoherent
    have himage {F G : Y.Modules} (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent)
        (f : F ⟶ G) : (imageSubobject f : Y.Modules).IsQuasicoherent := by
      letI := hF
      letI := hG
      haveI := Modules.isQuasicoherent_cokernel f
      have hk : (Abelian.image f).IsQuasicoherent :=
        Modules.isQuasicoherent_kernel (cokernel.π f)
      exact (quasiCoherentModuleProperty Y).prop_of_iso
        (Abelian.imageIsoImage f ≪≫ (imageSubobjectIso f).symm) hk
    have hpower : ∀ m, (coborderIdealPower i m).toModule.IsQuasicoherent := by
      intro m
      induction m with
      | zero =>
        exact (quasiCoherentModuleProperty Y).prop_of_iso
          (Subobject.underlyingIso (𝟙 (SheafOfModules.unit (structureSheaf Y)))).symm
          inferInstance
      | succ m ih =>
        letI := ih
        exact himage inferInstance inferInstance
          (Modules.action I (coborderIdealPower i m).toModule ≫
            (coborderIdealPower i m).arrow)
    letI := hpower n
    haveI : (Modules.toComm (coborderIdealPower i n).toModule).IsQuasicoherent := by
      change (coborderIdealPower i n).toModule.IsQuasicoherent
      exact hpower n
    haveI : (Modules.toCommSubobject I : RingedSite.ModuleCat (commRingedSite Y)).IsQuasicoherent :=
      (quasiCoherentModuleProperty Y).prop_of_iso
        (Subobject.underlyingIso (Modules.toCommArrow I)).symm
        (show I.toModule.IsQuasicoherent from inferInstance)
    haveI : (Modules.ofComm
        (tensorObj (Modules.toCommSubobject I : RingedSite.ModuleCat (commRingedSite Y))
          (Modules.toComm (coborderIdealPower i n).toModule))).IsQuasicoherent :=
      Modules.isQuasicoherent_tensor (X := Y) _ _
    exact Modules.isQuasicoherent_cokernel
      (Modules.idealAction I (coborderIdealPower i n).toModule)

/-- The degree-`n` conormal piece is a quasi-coherent `𝒪_Z`-module. -/
instance instIsQuasicoherent_piece (n : ℕ) : (piece i n).IsQuasicoherent :=
  Modules.pullback_isQuasicoherent (IsImmersion.liftCoborder i) (coborderQuotient i n)

/-- In degree one, the coborder successive quotient is `I / I²`. -/
theorem coborderQuotient_one :
    coborderQuotient i 1 =
      Modules.quotientByIdeal
        (Hom.idealSheafSubobject (IsImmersion.liftCoborder i))
        (Hom.idealSheaf (IsImmersion.liftCoborder i)) :=
  by
    rw [coborderQuotient, coborderIdealPower_one]

/-- The degree-one conormal piece is the conormal sheaf `C_{Z/X}`. -/
theorem piece_one : piece i 1 = Hom.conormalSheaf i :=
  by
    change (Modules.pullback (IsImmersion.liftCoborder i)).obj (coborderQuotient i 1) = _
    rw [coborderQuotient_one]
    rfl

/-- The degree-zero comparison `C_{Z/X, 0} ⟶ 𝒪_Z` obtained from the coborder
quotient comparison `I^0 / I ⟶ j_* j^* I^0`, the adjunction counit, and the
structure-module pullback of `I^0`. -/
noncomputable def pieceZeroComparison :
    piece i 0 ⟶ SheafOfModules.unit (structureSheaf Z) :=
  (Modules.pullback (IsImmersion.liftCoborder i)).map
      (Modules.quotientByIdealComparison (IsImmersion.liftCoborder i)
        (coborderIdealPower i 0).toModule) ≫
    (Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).counit.app
      ((Modules.pullback (IsImmersion.liftCoborder i)).obj
        (coborderIdealPower i 0).toModule) ≫
    IdealSubobject.pullbackMap (coborderIdealPower i 0) (IsImmersion.liftCoborder i)

/-- `pieceZeroComparison i` is the composite of the coborder quotient
comparison, the adjunction counit, and the structure-module pullback of `I^0`. -/
theorem pieceZeroComparison_eq :
    pieceZeroComparison i =
      (Modules.pullback (IsImmersion.liftCoborder i)).map
          (Modules.quotientByIdealComparison (IsImmersion.liftCoborder i)
            (coborderIdealPower i 0).toModule) ≫
        (Modules.pullbackPushforwardAdjunction (IsImmersion.liftCoborder i)).counit.app
          ((Modules.pullback (IsImmersion.liftCoborder i)).obj
            (coborderIdealPower i 0).toModule) ≫
        IdealSubobject.pullbackMap (coborderIdealPower i 0)
          (IsImmersion.liftCoborder i) :=
  rfl

/-- The degree-zero conormal piece is identified with `𝒪_Z` by
`pieceZeroComparison`. -/
instance piece_zero : IsIso (pieceZeroComparison i) :=
  sorry

/-- For an immersion of algebraic spaces, the degree-`n` piece
`C_{Z/X, n}` of the conormal algebra is characterized by the canonical
closed-immersion identification
`(liftCoborder i)_* C_{Z/X, n} ≅ I^n / I^{n+1}` on the coborder `X \ ∂Z`,
as the adjunction unit `I^n / I^{n+1} ⟶ (liftCoborder i)_* C_{Z/X, n}`. -/
@[stacks 09RP, instance]
theorem piece_pushforward (n : ℕ) :
    IsIso (piecePushforwardComparison i n) :=
  by
    let j := IsImmersion.liftCoborder i
    let adj := Modules.pullbackPushforwardAdjunction j
    let e := asIso (Modules.quotientByIdealComparison j (coborderIdealPower i n).toModule)
    letI := adj.fullyFaithfulROfIsIsoCounit.full
    letI := adj.fullyFaithfulROfIsIsoCounit.faithful
    exact adj.isIso_unit_app_of_iso e


end AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra

