module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Category.Grp.Ulift

@[expose] public section
open CategoryTheory
noncomputable section
universe u v
namespace SheafOfModules.UniverseLift

/-- Explicit ULift of the supplied ring homomorphism. -/
def ringHom {R S : RingCat.{u}} (f : R ⟶ S) :
    RingCat.of (ULift.{u+1} R) ⟶ RingCat.of (ULift.{u+1} S) :=
  RingCat.ofHom
    { toFun := fun x => ULift.up (f.hom x.down)
      map_zero' := congrArg ULift.up f.hom.map_zero
      map_one' := congrArg ULift.up f.hom.map_one
      map_add' := fun x y => congrArg ULift.up (f.hom.map_add x.down y.down)
      map_mul' := fun x y => congrArg ULift.up (f.hom.map_mul x.down y.down) }

/-- Both ring carriers and ring homomorphisms are the actual ULift data. -/
def ringFunctor : RingCat.{u} ⥤ RingCat.{u + 1} where
  obj R := RingCat.of (ULift.{u+1} R)
  map f := ringHom f
  map_id R := by ext x; rfl
  map_comp f g := by ext x; rfl

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})

/-- Lifting the displayed ring sheaf preserves its sheaf law; all carriers
and gluing functions are the ordinary ULift of the given sheaf. -/
theorem ring_isSheaf : Presheaf.IsSheaf J (R.obj ⋙ ringFunctor) := by sorry

def ring : Sheaf J RingCat.{u+1} := ⟨R.obj ⋙ ringFunctor, ring_isSheaf R⟩

instance liftedModule (M : SheafOfModules.{u} R) (V : Cᵒᵖ) :
    Module ((ring R).obj.obj V) (ULift.{u+1} (M.val.obj V)) :=
  inferInstanceAs (Module (ULift.{u+1} (R.obj.obj V)) (ULift.{u+1} (M.val.obj V)))

set_option backward.isDefEq.respectTransparency false in
/-- Lift module carriers, scalar action, restriction and morphisms explicitly. -/
def presheaf (M : SheafOfModules.{u} R) : PresheafOfModules.{u+1} (ring R).obj where
  obj V := ModuleCat.of ((ring R).obj.obj V) (ULift.{u+1} (M.val.obj V))
  map {V W} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((ring R).obj.map f).hom).obj
      (ModuleCat.of ((ring R).obj.obj W) (ULift.{u+1} (M.val.obj W))))
    { toFun := fun x => ULift.up (M.val.map f x.down)
      map_add' := by intros; apply ULift.ext; exact (M.val.map f).hom.map_add _ _
      map_smul' := by intros; apply ULift.ext; exact M.val.map_smul f _ _ }
  map_id := by sorry
  map_comp := by sorry

/-- The actual lifted additive presheaf is a sheaf by ULift of the given
unique amalgamation; this proposition selects no new module data. -/
theorem module_isSheaf (M : SheafOfModules.{u} R) :
    Presheaf.IsSheaf J (presheaf R M).presheaf := by
  let e : (presheaf R M).presheaf ≅
      M.val.presheaf ⋙ AddCommGrpCat.uliftFunctor.{u+1} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  apply (Presheaf.isSheaf_of_iso_iff e).mpr
  exact Presheaf.isSheaf_comp_of_isSheaf J M.val.presheaf
    AddCommGrpCat.uliftFunctor M.isSheaf

def obj (M : SheafOfModules.{u} R) : SheafOfModules.{u+1} (ring R) :=
  ⟨presheaf R M, module_isSheaf R M⟩

def map {M N : SheafOfModules.{u} R} (f : M ⟶ N) : obj R M ⟶ obj R N where
  val :=
    { app V := ModuleCat.ofHom
        { toFun := fun x => ULift.up (f.val.app V x.down)
          map_add' := by intros; apply ULift.ext; exact (f.val.app V).hom.map_add _ _
          map_smul' := by intros; apply ULift.ext; exact (f.val.app V).hom.map_smul _ _ }
      naturality := by sorry }

def functor : SheafOfModules.{u} R ⥤ SheafOfModules.{u+1} (ring R) where
  obj := obj R
  map := map R
  map_id := by sorry
  map_comp := by sorry

/-- No implicit reinterpretation of carriers: sections are literally ULift. -/
theorem obj_carrier (M : SheafOfModules.{u} R) (V : Cᵒᵖ) :
    ((obj R M).val.obj V : Type (u+1)) = ULift.{u+1} (M.val.obj V) := rfl

theorem restriction_up (M : SheafOfModules.{u} R) {V W : Cᵒᵖ} (f : V ⟶ W)
    (x : M.val.obj V) : (obj R M).val.map f (ULift.up x) = ULift.up (M.val.map f x) := rfl

theorem map_up {M N : SheafOfModules.{u} R} (f : M ⟶ N) (V : Cᵒᵖ) (x : M.val.obj V) :
    ((functor R).map f).val.app V (ULift.up x) = ULift.up (f.val.app V x) := rfl

/-- Lifting an already specified presheaf ring map applies ULift to that map. -/
def ringMap {D : Type (u+1)} [Category.{u} D] (F : C ⥤ D)
    {K : GrothendieckTopology D} (T : Sheaf K RingCat.{u})
    (η : F.op ⋙ T.obj ⟶ R.obj) : F.op ⋙ (ring T).obj ⟶ (ring R).obj :=
  Functor.whiskerRight η ringFunctor

end SheafOfModules.UniverseLift
