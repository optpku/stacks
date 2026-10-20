module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R S : Sheaf J RingCat.{w}}

/-- The actual forward and backward coefficient maps compose to the identity. -/
theorem restrictScalarsRoundTrip_ringHom_comp (e : R ≅ S) (U : Cᵒᵖ) :
    RingHom.id (R.obj.obj U) = (e.inv.hom.app U).hom.comp (e.hom.hom.app U).hom := by
  have h := NatTrans.congr_app (congrArg (fun f ↦ f.hom) e.hom_inv_id) U
  exact (congrArg RingCat.Hom.hom h).symm

/-- Restriction along a ring-sheaf isomorphism and its given inverse returns
the original module sheaf. Both component maps are the identity function. -/
def restrictScalarsRoundTrip (e : R ≅ S) (M : SheafOfModules.{z} R) :
    M ≅ (restrictScalars e.hom).obj ((restrictScalars e.inv).obj M) :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      ((_root_.ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)).symm ≪≫
        _root_.ModuleCat.restrictScalarsComp'App
          (e.hom.hom.app U).hom (e.inv.hom.app U).hom
          (RingHom.id (R.obj.obj U)) (restrictScalarsRoundTrip_ringHom_comp e U)
          (M.val.obj U)) (by sorry))

@[simp]
theorem restrictScalarsRoundTrip_hom_app (e : R ≅ S) (M : SheafOfModules.{z} R)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((restrictScalarsRoundTrip e M).hom.val.app U).hom x = x := rfl

@[simp]
theorem restrictScalarsRoundTrip_inv_app (e : R ≅ S) (M : SheafOfModules.{z} R)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((restrictScalarsRoundTrip e M).inv.val.app U).hom x = x := rfl

/-- An actual ring-sheaf isomorphism gives inverse scalar-restriction functors. -/
def restrictScalarsEquivalence (e : R ≅ S) :
    SheafOfModules.{z} R ≌ SheafOfModules.{z} S where
  functor := restrictScalars e.inv
  inverse := restrictScalars e.hom
  unitIso := NatIso.ofComponents (restrictScalarsRoundTrip e) (by sorry)
  counitIso := (NatIso.ofComponents (restrictScalarsRoundTrip e.symm) (by sorry)).symm
  functor_unitIso_comp := sorry

/-- Restriction of scalars along an isomorphism of sheaves of rings is a right adjoint.
The inverse functor uses the inverse supplied by the isomorphism premise. -/
noncomputable instance restrictScalars_isRightAdjoint_of_isIso
    (α : R ⟶ S) [IsIso α] :
    (SheafOfModules.restrictScalars.{z} α).IsRightAdjoint :=
  (restrictScalarsEquivalence (asIso α)).isRightAdjoint_inverse

end SheafOfModules.ChangeOfRings

end
