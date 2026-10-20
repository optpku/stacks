module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.CategoryTheory.Sites.Chaotic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver

/-!
# Affine objects of a category fibred in groupoids

The full subcategory `𝒳_affine` of objects of a category fibred in groupoids
over `(Sch/S)_fppf` that lie over affine schemes, equipped with the chaotic
topology and the universe-lifted commutative structure sheaf obtained by
restricting global sections along the projection.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- The property of objects of a category fibred in groupoids that lie over an
affine scheme. -/
def affineObjects : ObjectProperty X.total :=
  fun x ↦ IsAffine (X.p.obj x).left

/-- An object lies in `affineObjects X` if and only if its image scheme is
affine. -/
theorem affineObjects_iff (x : X.total) :
    affineObjects X x ↔ IsAffine (X.p.obj x).left :=
  sorry

/-- The full subcategory `𝒳_affine` of objects lying over affine schemes. -/
abbrev affineSite := (affineObjects X).FullSubcategory

/-- The inclusion of `𝒳_affine` into the total category of `X`. -/
abbrev affineInclusion : affineSite X ⥤ X.total :=
  (affineObjects X).ι

/-- The inclusion of an affine object is the underlying object of `X`. -/
theorem affineInclusion_obj (x : affineSite X) :
    (affineInclusion X).obj x = x.obj :=
  sorry

/-- The restricted projection `𝒳_affine ⥤ Sch/S`. -/
abbrev affineToOver : affineSite X ⥤ Over S :=
  affineInclusion X ⋙ X.p

/-- `affineToOver X` is the projection of `X` composed with the affine
inclusion. -/
theorem affineToOver_eq : affineToOver X = affineInclusion X ⋙ X.p :=
  sorry

/-- Every object of `affineSite X` lies over an affine scheme. -/
instance instIsAffine (x : affineSite X) : IsAffine (X.p.obj x.obj).left :=
  x.property

/-- The projection from affine objects to affine schemes over the base. -/
def affineSiteToAffineOver : affineSite X ⥤ S.AffineOver where
  obj x := Scheme.AffineOver.mk (X.p.obj x.obj).left x.property (X.p.obj x.obj).hom
  map f := Scheme.AffineOver.homMk (X.p.map f.hom).left (Over.w (X.p.map f.hom))
  map_id x := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    apply InducedCategory.hom_ext
    exact congrArg (fun f ↦ f.left) (X.p.map_id x.obj)
  map_comp f g := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    apply InducedCategory.hom_ext
    exact congrArg (fun f ↦ f.left) (X.p.map_comp f.hom g.hom)

/-- The affine projection sends an object to its underlying affine scheme over the base. -/
theorem affineSiteToAffineOver_obj (x : affineSite X) :
    (affineSiteToAffineOver X).obj x =
      Scheme.AffineOver.mk (X.p.obj x.obj).left x.property (X.p.obj x.obj).hom := rfl

/-- The affine projection sends a morphism to its underlying scheme morphism. -/
theorem affineSiteToAffineOver_map {x y : affineSite X} (f : x ⟶ y) :
    (Scheme.AffineOver.toScheme S).map ((affineSiteToAffineOver X).map f) =
      (X.p.map f.hom).left := rfl

/-- The chaotic commutative structure sheaf `𝒪` on `𝒳_affine`, obtained by
restricting universe-lifted global sections along the projection. -/
def affineStructureSheaf :
    Sheaf (⊥ : GrothendieckTopology (affineSite X)) CommRingCat.{u + 1} :=
  ⟨Scheme.Over.commStructurePresheaf (affineToOver X), Presheaf.isSheaf_bot _⟩

/-- The underlying presheaf of `affineStructureSheaf X` is the universe-lifted
global-sections presheaf of the restricted projection. -/
theorem affineStructureSheaf_obj :
    (affineStructureSheaf X).obj = Scheme.Over.commStructurePresheaf (affineToOver X) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
