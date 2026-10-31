/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Bundled
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.TwoCell
public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalIso
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Lift

/-!
# Two-fibre products of predeformation categories

A square of groupoid fibrations induces a square of predeformation categories
at a chosen residue object. The induced square preserves the bilimit property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
section Square

variable {W X Y Z : GroupoidsOver S}
variable (fX : X ⟶ Y) (gZ : Z ⟶ Y) (fW : W ⟶ X) (gW : W ⟶ Z)
variable (sq : fW ≫ fX ≅ gW ≫ gZ)
variable (w0 : W.p.Fiber (Over.mk kToS))

/-- Residue-fibre identification of the two images of `w0` in `Y`, extracted from the
`2`-cell of a `2`-commutative square. -/
def residueIso :
    residueImage gZ (residueImage gW w0) ≅ residueImage fX (residueImage fW w0) :=
  (BasedNatIso.fiber (Bicategory.InducedBicategory.Iso.toAmbient sq).symm
    (Over.mk kToS)).app w0

/-- The forward component of `residueIso` is the fibrewise action of `sq.inv` on `w0`. -/
theorem residueIso_hom :
    Functor.Fiber.fiberInclusion.map (residueIso kToS fX gZ fW gW sq w0).hom =
      (toNatTrans sq.inv).app (Functor.Fiber.fiberInclusion.obj w0) :=
  rfl

/-- The inverse component of `residueIso` is the fibrewise action of `sq.hom` on `w0`. -/
theorem residueIso_inv :
    Functor.Fiber.fiberInclusion.map (residueIso kToS fX gZ fW gW sq w0).inv =
      (toNatTrans sq.hom).app (Functor.Fiber.fiberInclusion.obj w0) :=
  rfl

/-- Natural transformation of total functors filling the image of a `2`-commutative
square of groupoid fibrations. -/
private def mapCone_homNT :
    (map openImmersion h_factor fW w0).toFunctor ⋙
        (map openImmersion h_factor fX (residueImage fW w0)).toFunctor ⟶
      (map openImmersion h_factor gW w0).toFunctor ⋙
        mapFunctorAlong openImmersion kToS h_factor gZ
          (residueIso kToS fX gZ fW gW sq w0) := by
  let F := (map openImmersion h_factor fW w0).toFunctor ⋙
      (map openImmersion h_factor fX (residueImage fW w0)).toFunctor
  let G := (map openImmersion h_factor gW w0).toFunctor ⋙
      mapFunctorAlong openImmersion kToS h_factor gZ
        (residueIso kToS fX gZ fW gW sq w0)
  let component (ξ : Obj openImmersion kToS h_factor W w0) :=
    (toNatTrans sq.inv).app (Functor.Fiber.fiberInclusion.obj ξ.target)
  let Compatible : Prop := ∀ ξ : Obj openImmersion kToS h_factor W w0,
    Y.p.IsHomLift (specOverMap openImmersion (𝟙 ξ.base)) (component ξ) ∧
      (F.obj ξ).fromResidue = (G.obj ξ).fromResidue ≫ component ξ
  have laws : Compatible ∧
      (∀ h : Compatible,
        ∀ (ξ η : Obj openImmersion kToS h_factor W w0) (f : ξ ⟶ η),
          F.map f ≫ Hom.of (ξ := F.obj η) (η := G.obj η) (𝟙 η.base) (component η) (h η).1 (h η).2 =
            Hom.of (ξ := F.obj ξ) (η := G.obj ξ) (𝟙 ξ.base) (component ξ) (h ξ).1 (h ξ).2 ≫ G.map f) := by
    sorry
  exact
    { app ξ := Hom.of (ξ := F.obj ξ) (η := G.obj ξ) (𝟙 ξ.base) (component ξ) (laws.1 ξ).1 (laws.1 ξ).2
      naturality := fun ξ η f => laws.2 laws.1 ξ η f }

/-- Inverse natural transformation filling the image of a `2`-commutative square. -/
private def mapCone_invNT :
    (map openImmersion h_factor gW w0).toFunctor ⋙
        mapFunctorAlong openImmersion kToS h_factor gZ
          (residueIso kToS fX gZ fW gW sq w0) ⟶
      (map openImmersion h_factor fW w0).toFunctor ⋙
        (map openImmersion h_factor fX (residueImage fW w0)).toFunctor := by
  let F := (map openImmersion h_factor gW w0).toFunctor ⋙
      mapFunctorAlong openImmersion kToS h_factor gZ
        (residueIso kToS fX gZ fW gW sq w0)
  let G := (map openImmersion h_factor fW w0).toFunctor ⋙
      (map openImmersion h_factor fX (residueImage fW w0)).toFunctor
  let component (ξ : Obj openImmersion kToS h_factor W w0) :=
    (toNatTrans sq.hom).app (Functor.Fiber.fiberInclusion.obj ξ.target)
  let Compatible : Prop := ∀ ξ : Obj openImmersion kToS h_factor W w0,
    Y.p.IsHomLift (specOverMap openImmersion (𝟙 ξ.base)) (component ξ) ∧
      (F.obj ξ).fromResidue = (G.obj ξ).fromResidue ≫ component ξ
  have laws : Compatible ∧
      (∀ h : Compatible,
        ∀ (ξ η : Obj openImmersion kToS h_factor W w0) (f : ξ ⟶ η),
          F.map f ≫ Hom.of (ξ := F.obj η) (η := G.obj η) (𝟙 η.base) (component η) (h η).1 (h η).2 =
            Hom.of (ξ := F.obj ξ) (η := G.obj ξ) (𝟙 ξ.base) (component ξ) (h ξ).1 (h ξ).2 ≫ G.map f) := by
    sorry
  exact
    { app ξ := Hom.of (ξ := F.obj ξ) (η := G.obj ξ) (𝟙 ξ.base) (component ξ) (laws.1 ξ).1 (laws.1 ξ).2
      naturality := fun ξ η f => laws.2 laws.1 ξ η f }

/-- Functor isomorphism filling the image of a `2`-commutative square. -/
private def mapCone_functorIso :
    (map openImmersion h_factor fW w0).toFunctor ⋙
        (map openImmersion h_factor fX (residueImage fW w0)).toFunctor ≅
      (map openImmersion h_factor gW w0).toFunctor ⋙
        mapFunctorAlong openImmersion kToS h_factor gZ
          (residueIso kToS fX gZ fW gW sq w0) := by
  let hom := mapCone_homNT openImmersion kToS h_factor fX gZ fW gW sq w0
  let inv := mapCone_invNT openImmersion kToS h_factor fX gZ fW gW sq w0
  have laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := by
    sorry
  exact { hom := hom, inv := inv, hom_inv_id := laws.1, inv_hom_id := laws.2 }

/-- Based-functor isomorphism filling the image of a `2`-commutative square. -/
@[no_expose]
def mapCone_iso :
    BasedFunctor.comp (map openImmersion h_factor fW w0)
        (map openImmersion h_factor fX (residueImage fW w0)) ≅
      BasedFunctor.comp (map openImmersion h_factor gW w0)
        (mapBasedFunctorAlong openImmersion kToS h_factor gZ
          (residueIso kToS fX gZ fW gW sq w0)) := by
  let e := mapCone_functorIso openImmersion kToS h_factor fX gZ fW gW sq w0
  have compatibility : ∀ ξ : Obj openImmersion kToS h_factor W w0,
      (forget openImmersion kToS h_factor Y (residueImage fX (residueImage fW w0))).IsHomLift
        (𝟙 ξ.base)
        (e.hom.app ξ) := by
    sorry
  exact BasedNatIso.mkNatIso e compatibility

/-- The readable pseudopullback cone of predeformation categories induced by a
`2`-commutative square of categories fibered in groupoids. -/
def mapCone :
    Bicategory.PseudoPullbackCone
      (mapBundled openImmersion kToS h_factor fX (residueImage fW w0))
      (mapAlong openImmersion kToS h_factor gZ
        (residueIso kToS fX gZ fW gW sq w0)) where
  pt := bundled openImmersion kToS h_factor W w0
  fst := mapBundled openImmersion kToS h_factor fW w0
  snd := mapBundled openImmersion kToS h_factor gW w0
  iso := Bicategory.InducedBicategory.isoMk
    (mapCone_iso openImmersion kToS h_factor fX gZ fW gW sq w0)

/-- The apex of `mapCone` is the predeformation category of `W` at `w0`. -/
theorem mapCone_pt :
    (mapCone openImmersion kToS h_factor fX gZ fW gW sq w0).pt =
      bundled openImmersion kToS h_factor W w0 :=
  rfl

/-- The comparison from the induced cone of predeformation categories into the explicit
two-fibre product retains the cone's two legs and invertible comparison. -/
def comparison :
    bundled openImmersion kToS h_factor W w0 ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (mapBundled openImmersion kToS h_factor fX (residueImage fW w0))
        (mapAlong openImmersion kToS h_factor gZ
          (residueIso kToS fX gZ fW gW sq w0)) :=
  TwoFibreProduct.lift (mapCone openImmersion kToS h_factor fX gZ fW gW sq w0)

end Square

/-- A two-fibre-product square of groupoid fibrations induces a bilimit square of
predeformation categories at any chosen residue object. -/
instance mapCone_isBilimit {S : Scheme.{u}} [IsLocallyNoetherian S]
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    {W X Y Z : GroupoidsOver S} (fX : X ⟶ Y) (gZ : Z ⟶ Y) (fW : W ⟶ X) (gW : W ⟶ Z)
    (sq : fW ≫ fX ≅ gW ≫ gZ) (w0 : W.p.Fiber (Over.mk kToS))
    [hW : Bicategory.PseudoPullbackCone.IsBilimit
      (⟨W, fW, gW, sq⟩ : Bicategory.PseudoPullbackCone fX gZ)] :
    (mapCone openImmersion kToS h_factor fX gZ fW gW sq w0).IsBilimit :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
