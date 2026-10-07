module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import stacks_project.Chap93.Example_93_9_1_Schemes_Deformation

/-!
# Restriction of scheme deformations to an open subscheme

A morphism `(f, g) : (B, Y) ⟶ (A, X)` of flat scheme pairs has a
corresponding open of `Y` for each open `U ⊂ X`. Restricting along that
open yields a functor `Def_X ⥤ Def_U` of deformation categories over
`ArtinianLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

namespace FlatSchemeCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace Hom

variable {Λ k}

/-- The image of an open of the target scheme is open in the source scheme,
because a morphism of `FlatSchemeCat` is a cartesian Artinian thickening. -/
theorem isOpen_image {src tgt : FlatSchemeCat Λ k} (f : src ⟶ tgt)
    (U : tgt.scheme.Opens) :
    IsOpen (Set.image (fun x ↦ f.schemeHom x) (U : Set tgt.scheme)) :=
  sorry

/-- The corresponding open of the source scheme attached to `U ⊂ tgt.scheme`. -/
def correspondingOpen {src tgt : FlatSchemeCat Λ k} (f : src ⟶ tgt)
    (U : tgt.scheme.Opens) : src.scheme.Opens where
  carrier := Set.image (fun x ↦ f.schemeHom x) (U : Set tgt.scheme)
  is_open' := f.isOpen_image U

/-- The carrier of `correspondingOpen` is the image of `U` under `schemeHom`. -/
theorem correspondingOpen_carrier {src tgt : FlatSchemeCat Λ k} (f : src ⟶ tgt)
    (U : tgt.scheme.Opens) :
    (f.correspondingOpen U : Set src.scheme) =
      Set.image (fun x ↦ f.schemeHom x) (U : Set tgt.scheme) :=
  sorry

/-- Membership in the corresponding open is membership in the `schemeHom`-image. -/
theorem mem_correspondingOpen {src tgt : FlatSchemeCat Λ k} (f : src ⟶ tgt)
    {U : tgt.scheme.Opens} {y : src.scheme} :
    y ∈ f.correspondingOpen U ↔
      ∃ x ∈ (U : Set tgt.scheme), f.schemeHom x = y :=
  sorry

end Hom

/-- The restricted pair `(A, U_Y)` attached to a deformation `(A, Y) ⟶ (k, X)`. -/
def restrictObj (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens)
    (ξ : deformationCategory Λ k X hX) : FlatSchemeCat Λ k :=
  of ξ.left.base (ξ.hom.correspondingOpen U).toScheme
    ((ξ.hom.correspondingOpen U).ι ≫ ξ.left.structureHom)

/-- The restricted pair keeps the original Artinian local base. -/
theorem restrictObj_base (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens)
    (ξ : deformationCategory Λ k X hX) :
    (restrictObj Λ k X hX U ξ).base = ξ.left.base :=
  sorry

/-- The cartesian morphism `(A, U_Y) ⟶ (k, U)` of the restricted deformation. -/
def restrictHom (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens)
    (ξ : deformationCategory Λ k X hX) :
    restrictObj Λ k X hX U ξ ⟶ ofResidue Λ k U.toScheme (U.ι ≫ hX) where
  baseHom := ξ.hom.baseHom
  schemeHom :=
    ξ.hom.schemeHom.resLE (ξ.hom.correspondingOpen U) U (fun x hx ↦ ⟨x, hx, rfl⟩)
  isPullback := sorry

/-- The restricted deformation keeps the original base morphism `A ⟶ k`. -/
theorem restrictHom_baseHom (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens)
    (ξ : deformationCategory Λ k X hX) :
    (restrictHom Λ k X hX U ξ).baseHom = ξ.hom.baseHom :=
  sorry

/-- A morphism of deformations of `X` restricts to corresponding opens of `U`. -/
def restrictMap (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens)
    {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    restrictObj Λ k X hX U ξ ⟶ restrictObj Λ k X hX U η where
  baseHom := φ.left.baseHom
  schemeHom :=
    φ.left.schemeHom.resLE (ξ.hom.correspondingOpen U) (η.hom.correspondingOpen U)
      (fun y ⟨x, hxU, hxy⟩ ↦
        ⟨x, hxU,
          (congrArg (fun h ↦ h.schemeHom x) (Over.w φ)).symm.trans
            (congrArg (fun z ↦ φ.left.schemeHom z) hxy)⟩)
  isPullback := sorry

/-- Restricted morphisms commute with the structure maps to `(k, U)`. -/
theorem restrictMap_w (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens)
    {ξ η : deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    restrictMap Λ k X hX U φ ≫ restrictHom Λ k X hX U η =
      restrictHom Λ k X hX U ξ :=
  sorry

/-- The ordinary functor `Def_X ⥤ Def_U` sending a deformation of `X` to the
corresponding open deformation of `U`. -/
def restrictFunctor (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens) :
    deformationCategory Λ k X hX ⥤ deformationCategory Λ k U.toScheme (U.ι ≫ hX) where
  obj ξ := Over.mk (restrictHom Λ k X hX U ξ)
  map φ := Over.homMk (restrictMap Λ k X hX U φ) (restrictMap_w Λ k X hX U φ)
  map_id := sorry
  map_comp := sorry

/-- Objects of `restrictFunctor` are the restricted deformations `(A, U_Y) ⟶ (k, U)`. -/
theorem restrictFunctor_obj (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens)
    (ξ : deformationCategory Λ k X hX) :
    (restrictFunctor Λ k X hX U).obj ξ = Over.mk (restrictHom Λ k X hX U ξ) :=
  sorry

/-- `restrictFunctor` lies strictly over `ArtinianLocalAlgCat`. -/
theorem restrictFunctor_comp_forget (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens) :
    restrictFunctor Λ k X hX U ⋙
        Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k U.toScheme (U.ι ≫ hX))) ⋙
          forget Λ k =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k :=
  sorry

/-- The morphism `Def_X ⥤ᵇ Def_U` of categories over `ArtinianLocalAlgCat`. -/
def restrictOpen (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens) :
    BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k) ⥤ᵇ
      BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k U.toScheme (U.ι ≫ hX))) ⋙
          forget Λ k) :=
  BasedFunctor.ofFunctor (restrictFunctor Λ k X hX U)
    (restrictFunctor_comp_forget Λ k X hX U)

/-- The underlying ordinary functor of `restrictOpen` is `restrictFunctor`. -/
theorem restrictOpen_toFunctor (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (U : X.Opens) :
    (restrictOpen Λ k X hX U).toFunctor = restrictFunctor Λ k X hX U :=
  sorry

end FlatSchemeCat

end
