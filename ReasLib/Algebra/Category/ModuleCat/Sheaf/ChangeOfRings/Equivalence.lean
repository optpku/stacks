/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R R' R'' : Sheaf J RingCat.{w}}

/-- Restriction of scalars along a composite ring-sheaf map is naturally isomorphic to
the composite of the corresponding restriction functors. -/
private noncomputable def restrictScalarsCompIso
    (α : R ⟶ R') (β : R' ⟶ R'') (γ : R ⟶ R'') (h : γ = α ≫ β) :
    SheafOfModules.restrictScalars γ ≅
      SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · let e : (PresheafOfModules.restrictScalars γ.hom).obj M.val ≅
        (PresheafOfModules.restrictScalars α.hom).obj
          ((PresheafOfModules.restrictScalars β.hom).obj M.val) :=
      PresheafOfModules.isoMk (fun X => by
        dsimp [PresheafOfModules.restrictScalars, PresheafOfModules.restrictScalarsObj]
        exact ModuleCat.restrictScalarsComp'App
          (α.hom.app X).hom (β.hom.app X).hom (γ.hom.app X).hom (by
            rw [h]
            rfl) (M.val.obj X))
    exact { hom := ⟨e.hom⟩, inv := ⟨e.inv⟩ }
  · intro X Y f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro Z
    rfl

/-- Restriction of scalars along the identity ring-sheaf map is naturally isomorphic to the
identity functor. -/
private noncomputable def restrictScalarsIdIso (R : Sheaf J RingCat.{w}) :
    SheafOfModules.restrictScalars (𝟙 R) ≅ 𝟭 (SheafOfModules R) := Iso.refl _

/-- Restriction of scalars along an isomorphism of sheaves of rings is a right adjoint. -/
noncomputable instance restrictScalars_isRightAdjoint_of_isIso
    (α : R ⟶ R') [IsIso α] :
    (SheafOfModules.restrictScalars α).IsRightAdjoint := by
  let β : R' ⟶ R := inv α
  let e : SheafOfModules R' ≌ SheafOfModules R :=
    { functor := SheafOfModules.restrictScalars α
      inverse := SheafOfModules.restrictScalars β
      unitIso := (restrictScalarsIdIso R').symm ≪≫
        restrictScalarsCompIso β α (𝟙 R') (by
          change 𝟙 R' = inv α ≫ α
          exact (IsIso.inv_hom_id α).symm)
      counitIso := (restrictScalarsCompIso α β (𝟙 R) (by
          change 𝟙 R = α ≫ inv α
          exact (IsIso.hom_inv_id α).symm)).symm ≪≫
        restrictScalarsIdIso R }
  exact e.isRightAdjoint_functor

end SheafOfModules.ChangeOfRings

end
