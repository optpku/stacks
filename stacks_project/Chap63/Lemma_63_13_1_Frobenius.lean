module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import ReasLib.Algebra.CharP.Frobenius
public import ReasLib.AlgebraicGeometry.Scheme.Characteristic.Prime
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Standard

/-!
# Frobenius-semilinear endomorphisms on associated étale abelian sheaves

This leaf owns the associated small-étale abelian sheaf of a quasi-coherent
module, the sectionwise `p`-power map, Frobenius-semilinearity, and the
comparison morphism `F - 𝟙`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Frobenius

/-- The abelian sheaf on `S_étale` obtained by viewing a quasi-coherent
`𝒪_S`-module as a module on the small étale site. -/
noncomputable abbrev smallEtaleAbelian (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] :
    Sheaf S.smallEtaleTopology AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (Scheme.AssociatedModule.smallStructureSheaf .etale S)).obj
    (Scheme.AssociatedModule.small .etale S E)

/-- `smallEtaleAbelian` is the forgetful image of the associated small-étale
module sheaf. -/
theorem smallEtaleAbelian_eq (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent] :
    smallEtaleAbelian S E =
      (SheafOfModules.toSheaf
        (Scheme.AssociatedModule.smallStructureSheaf .etale S)).obj
        (Scheme.AssociatedModule.small .etale S E) := sorry

/-- The morphism `toScheme.obj U ⟶ S` induced by an étale object. -/
def etaleToBase {S : Scheme.{u}} (U : S.Etale) :
    (SmallStandardTopology.toScheme .etale S).obj U ⟶ S :=
  ((SmallStandardTopology.toOver .etale S).obj U).hom

/-- `etaleToBase` is the structure morphism of the étale object. -/
theorem etaleToBase_eq {S : Scheme.{u}} (U : S.Etale) :
    etaleToBase U = ((SmallStandardTopology.toOver .etale S).obj U).hom := sorry

/-- The `p`-power endomorphism of global sections of an étale scheme over a
characteristic-`p` base. -/
def etaleSectionFrobenius {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] [S.IsCharP p]
    (U : S.Etale) :
    Γ((SmallStandardTopology.toScheme .etale S).obj U, ⊤) →+*
      Γ((SmallStandardTopology.toScheme .etale S).obj U, ⊤) :=
  RingHom.frobeniusOfPrime p
    ((map_natCast (etaleToBase U).appTop.hom p).symm.trans
      ((congrArg (etaleToBase U).appTop.hom
          (IsCharP.cast_eq_zero (⊤ : S.Opens))).trans
        (map_zero (etaleToBase U).appTop.hom)))

/-- `etaleSectionFrobenius` sends a section `a` to `a ^ p`. -/
theorem etaleSectionFrobenius_apply {S : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    [S.IsCharP p] (U : S.Etale)
    (a : Γ((SmallStandardTopology.toScheme .etale S).obj U, ⊤)) :
    etaleSectionFrobenius p U a = a ^ p := sorry

/-- Structure-sheaf scalars act on associated étale abelian-sheaf sections via
the module structure of `AssociatedModule.small`. -/
def etaleSectionSMul {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    {U : S.Etale}
    (a : Γ((SmallStandardTopology.toScheme .etale S).obj U, ⊤))
    (e : (smallEtaleAbelian S E).obj.obj (op U)) :
    (smallEtaleAbelian S E).obj.obj (op U) :=
  let a' : (Scheme.AssociatedModule.smallStructureSheaf .etale S).obj.obj (op U) :=
    Eq.mp (CommRingCat.forgetToRingCat_obj
      (R := Scheme.Γ.obj
        (op ((SmallStandardTopology.toScheme .etale S).obj U)))).symm a
  let e' : (Scheme.AssociatedModule.small .etale S E).val.obj (op U) :=
    Eq.mp (PresheafOfModules.toPresheaf_obj_coe
      (M := (Scheme.AssociatedModule.small .etale S E).val) (op U)) e
  let y :=
    @SMul.smul
      ((Scheme.AssociatedModule.smallStructureSheaf .etale S).obj.obj (op U))
      ((Scheme.AssociatedModule.small .etale S E).val.obj (op U))
      (ModuleCat.isModule
        ((Scheme.AssociatedModule.small .etale S E).val.obj (op U))).toSMul
      a' e'
  Eq.mp (PresheafOfModules.toPresheaf_obj_coe
      (M := (Scheme.AssociatedModule.small .etale S E).val) (op U)).symm y

/-- Zero acts by zero on associated étale abelian-sheaf sections. -/
theorem etaleSectionSMul_zero {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    {U : S.Etale} (e : (smallEtaleAbelian S E).obj.obj (op U)) :
    etaleSectionSMul E
      (0 : Γ((SmallStandardTopology.toScheme .etale S).obj U, ⊤)) e = 0 :=
  sorry

/-- The unit of the structure sheaf acts as the identity on associated étale
abelian-sheaf sections. -/
theorem etaleSectionSMul_one {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    {U : S.Etale} (e : (smallEtaleAbelian S E).obj.obj (op U)) :
    etaleSectionSMul E
      (1 : Γ((SmallStandardTopology.toScheme .etale S).obj U, ⊤)) e = e :=
  sorry

/-- An abelian-sheaf endomorphism of the associated étale sheaf of `E` is
Frobenius-semilinear when it intertwines structure-sheaf scalars with the
`p`-power map. -/
def IsFrobeniusSemilinear {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] [S.IsCharP p]
    (E : S.Modules) [E.IsQuasicoherent]
    (F : smallEtaleAbelian S E ⟶ smallEtaleAbelian S E) : Prop :=
  ∀ (U : S.Etale)
    (a : Γ((SmallStandardTopology.toScheme .etale S).obj U, ⊤))
    (e : (smallEtaleAbelian S E).obj.obj (op U)),
    F.hom.app (op U) (etaleSectionSMul E a e) =
      etaleSectionSMul E (etaleSectionFrobenius p U a) (F.hom.app (op U) e)

/-- Frobenius-semilinearity is the sectionwise identity
`F (a • e) = etaleSectionFrobenius p U a • F e` on the small étale site. -/
theorem isFrobeniusSemilinear_iff {S : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    [S.IsCharP p] (E : S.Modules) [E.IsQuasicoherent]
    (F : smallEtaleAbelian S E ⟶ smallEtaleAbelian S E) :
    IsFrobeniusSemilinear p E F ↔
      ∀ (U : S.Etale)
        (a : Γ((SmallStandardTopology.toScheme .etale S).obj U, ⊤))
        (e : (smallEtaleAbelian S E).obj.obj (op U)),
        F.hom.app (op U) (etaleSectionSMul E a e) =
          etaleSectionSMul E (etaleSectionFrobenius p U a)
            (F.hom.app (op U) e) := sorry

/-- A Frobenius-semilinear endomorphism sends `etaleSectionSMul E a e` to
`etaleSectionSMul E (etaleSectionFrobenius p U a) (F e)`. -/
theorem isFrobeniusSemilinear_map_smul {S : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    [S.IsCharP p] (E : S.Modules) [E.IsQuasicoherent]
    (F : smallEtaleAbelian S E ⟶ smallEtaleAbelian S E)
    (hF : IsFrobeniusSemilinear p E F) (U : S.Etale)
    (a : Γ((SmallStandardTopology.toScheme .etale S).obj U, ⊤))
    (e : (smallEtaleAbelian S E).obj.obj (op U)) :
    F.hom.app (op U) (etaleSectionSMul E a e) =
      etaleSectionSMul E (etaleSectionFrobenius p U a)
        (F.hom.app (op U) e) := sorry

/-- The abelian-sheaf endomorphism `F - 𝟙` associated to an endomorphism of the
associated étale sheaf of `E`. -/
def subId {S : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent]
    [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    (F : smallEtaleAbelian S E ⟶ smallEtaleAbelian S E) :
    smallEtaleAbelian S E ⟶ smallEtaleAbelian S E :=
  F - 𝟙 _

/-- `subId F` is the difference `F - 𝟙`. -/
theorem subId_eq {S : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent]
    [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    (F : smallEtaleAbelian S E ⟶ smallEtaleAbelian S E) :
    subId F = F - 𝟙 _ := sorry

/-- On sections, `subId F` acts by `e ↦ F e - e`. -/
theorem subId_app {S : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent]
    [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    (F : smallEtaleAbelian S E ⟶ smallEtaleAbelian S E) (U : S.Etale)
    (e : (smallEtaleAbelian S E).obj.obj (op U)) :
    (subId F).hom.app (op U) e = F.hom.app (op U) e - e := sorry

end AlgebraicGeometry.Scheme.Etale.Frobenius

