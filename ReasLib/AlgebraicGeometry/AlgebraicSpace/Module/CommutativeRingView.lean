module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ScalarExtension

/-! # Keep the original ring-sheaf data while recording its commutativity

Only a multiplication law is added. Carriers, ring operations and all maps
are the original data. No ring or sheaf is chosen from an existence claim.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.CommutativeRingView

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf J RingCat.{w})
    (hc : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)

/-- Retain the given ring operations and add only their commutativity proof. -/
@[reducible] def commRing (U : Cᵒᵖ) : _root_.CommRing (R.obj.obj U) :=
  { (inferInstance : _root_.Ring (R.obj.obj U)) with mul_comm := hc U }

/-- The same carriers and same restriction functions with their commutative-ring view. -/
def presheaf : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj U := @CommRingCat.of (R.obj.obj U) (commRing R hc U)
  map {U V} i := @CommRingCat.ofHom _ _ (commRing R hc U) (commRing R hc V) (R.obj.map i).hom
  map_id U := by ext r; exact ConcreteCategory.congr_hom (R.obj.map_id U) r
  map_comp f g := by ext r; exact ConcreteCategory.congr_hom (R.obj.map_comp f g) r

theorem underlying_presheaf : presheaf R hc ⋙ forget₂ CommRingCat RingCat = R.obj := rfl

/-- Sheafness is reflected by forgetting commutativity of the identical ring diagram. -/
theorem isSheaf : Presheaf.IsSheaf J (presheaf R hc) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
  exact R.property

def sheaf : Sheaf J CommRingCat.{w} := ⟨presheaf R hc, isSheaf R hc⟩

theorem underlying_sheaf : CategoryTheory.Sheaf.ringSheafOfComm (sheaf R hc) = R := rfl

variable {R} {R' : Sheaf J RingCat.{w}}
    (hc' : ∀ (U : Cᵒᵖ) (a b : R'.obj.obj U), a * b = b * a)

/-- Same actual ring maps; the commutativity proof does not alter their functions. -/
def map (α : R ⟶ R') : sheaf R hc ⟶ sheaf R' hc' :=
  ⟨{ app U := @CommRingCat.ofHom _ _ (commRing R hc U) (commRing R' hc' U) (α.hom.app U).hom
     naturality := by intro U V i; ext r; exact ConcreteCategory.congr_hom (α.hom.naturality i) r }⟩

theorem underlying_map (α : R ⟶ R') :
    CategoryTheory.Sheaf.ringSheafOfCommMap (map hc hc' α) = α := rfl

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.CommutativeRingView
