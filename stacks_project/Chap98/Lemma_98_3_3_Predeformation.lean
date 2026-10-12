/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.TwoCell
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import stacks_project.Chap90.Remarks_90_5_2_Groupoids
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Lemma_98_3_1
public import stacks_project.Chap98.«98_3_1_1_Functor»

/-!
# Induced cones of predeformation categories

A 2-fibre product of categories fibered in groupoids over `Over S` induces a readable
pseudopullback cone of the associated predeformation categories over
`ArtinianLocalAlgCat Λ k`. Functoriality of `ℱ_{X, k, x0}` is the existing based functor
`map`; this module bundles it as a cofibered-groupoid 1-morphism and transports along the
residue-fibre identification of the two images of `w0` in `Y`.
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
variable (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))

/-- Cofibered-in-groupoids structure of `predeformationFunctor`, projected from the
canonical `IsPredeformationCategory` instance. -/
instance instIsFiberedInGroupoids_op :
    Functor.IsFibered.InGroupoids
      (predeformationFunctor X openImmersion kToS h_factor x0).op :=
  (instIsPredeformationCategory_predeformationFunctor
    X openImmersion kToS h_factor x0).isCofiberedInGroupoids

/-- The predeformation category `ℱ_{𝒳, k, x₀}` as a category cofibered in groupoids over
`ArtinianLocalAlgCat Λ k`. -/
def bundled :
    CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k) :=
  CofiberedCategoryOver.Groupoids.ofFunctor
    (predeformationFunctor X openImmersion kToS h_factor x0)

/-- The projection of `bundled X x0` is the forgetful functor of `ℱ_{𝒳, k, x₀}`. -/
theorem bundled_p :
    (bundled openImmersion kToS h_factor X x0).p =
      forget openImmersion kToS h_factor X x0 :=
  sorry

/-- Bundle the based functor `map φ x0` as a 1-morphism of categories cofibered in groupoids
over `ArtinianLocalAlgCat Λ k`. -/
def mapBundled {X Y : GroupoidsOver S} (φ : X ⟶ Y) (x0 : X.p.Fiber (Over.mk kToS)) :
    bundled openImmersion kToS h_factor X x0 ⟶
      bundled openImmersion kToS h_factor Y (residueImage φ x0) :=
  CofiberedCategoryOver.Groupoids.ofBasedFunctor (map openImmersion h_factor φ x0)

/-- Forgetting `mapBundled` to based functors recovers `map`. -/
theorem mapBundled_toBasedFunctor {X Y : GroupoidsOver S} (φ : X ⟶ Y)
    (x0 : X.p.Fiber (Over.mk kToS)) :
    CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapBundled openImmersion kToS h_factor φ x0) =
      map openImmersion h_factor φ x0 :=
  sorry

section MapAlong

variable {X Y : GroupoidsOver S} (φ : X ⟶ Y)
variable {x0 : X.p.Fiber (Over.mk kToS)} {y0 : Y.p.Fiber (Over.mk kToS)}
variable (α : residueImage φ x0 ≅ y0)

/-- Object map of `ℱ_{𝒳, k, x₀} → ℱ_{𝒴, k, y₀}` along a residue-fibre identification
`φ(x₀) ≅ y₀`. -/
def mapObjAlong (ξ : Obj openImmersion kToS h_factor X x0) :
    Obj openImmersion kToS h_factor Y y0 where
  base := ξ.base
  target := (fiberFunctor φ (specOver openImmersion ξ.base)).obj ξ.target
  fromResidue := Functor.Fiber.fiberInclusion.map α.inv ≫ (toFunctor φ).map ξ.fromResidue
  over_fromResidue := sorry

/-- The object map along a residue-fibre identification preserves the stored Artinian base. -/
theorem mapObjAlong_base (ξ : Obj openImmersion kToS h_factor X x0) :
    (mapObjAlong openImmersion kToS h_factor φ α ξ).base = ξ.base :=
  sorry

/-- Arrow map along a residue-fibre identification `φ(x₀) ≅ y₀`. -/
def mapHomAlong {ξ η : Obj openImmersion kToS h_factor X x0} (f : ξ ⟶ η) :
    mapObjAlong openImmersion kToS h_factor φ α ξ ⟶
      mapObjAlong openImmersion kToS h_factor φ α η where
  baseHom := f.baseHom
  hom := (toFunctor φ).map f.hom
  over_hom := sorry
  triangle := sorry

/-- The functor `ℱ_{𝒳, k, x₀} ⥤ ℱ_{𝒴, k, y₀}` along a residue-fibre identification. -/
def mapFunctorAlong : Obj openImmersion kToS h_factor X x0 ⥤
    Obj openImmersion kToS h_factor Y y0 where
  obj ξ := mapObjAlong openImmersion kToS h_factor φ α ξ
  map f := mapHomAlong openImmersion kToS h_factor φ α f
  map_id := sorry
  map_comp := sorry

/-- `mapFunctorAlong` lies strictly over `ArtinianLocalAlgCat Λ k`. -/
def mapBasedFunctorAlong :
    BasedCategory.ofFunctor (forget openImmersion kToS h_factor X x0) ⥤ᵇ
      BasedCategory.ofFunctor (forget openImmersion kToS h_factor Y y0) :=
  BasedFunctor.ofFunctor (mapFunctorAlong openImmersion kToS h_factor φ α) sorry

/-- The 1-morphism of predeformation categories along a residue-fibre identification. -/
def mapAlong : bundled openImmersion kToS h_factor X x0 ⟶
    bundled openImmersion kToS h_factor Y y0 :=
  CofiberedCategoryOver.Groupoids.ofBasedFunctor
    (mapBasedFunctorAlong openImmersion kToS h_factor φ α)

/-- Forgetting `mapAlong` to based functors recovers `mapBasedFunctorAlong`. -/
theorem mapAlong_toBasedFunctor :
    CofiberedCategoryOver.Groupoids.toBasedFunctor
        (mapAlong openImmersion kToS h_factor φ α) =
      mapBasedFunctorAlong openImmersion kToS h_factor φ α :=
  sorry

end MapAlong

section Square

variable {W X Y Z : GroupoidsOver S}
variable (fX : X ⟶ Y) (gZ : Z ⟶ Y) (fW : W ⟶ X) (gW : W ⟶ Z)
variable (sq : fW ≫ fX ≅ gW ≫ gZ)
variable (w0 : W.p.Fiber (Over.mk kToS))

/-- Residue-fibre identification of the two images of `w0` in `Y`, extracted from the
`2`-cell of a `2`-commutative square. -/
def residueIso :
    residueImage gZ (residueImage gW w0) ≅ residueImage fX (residueImage fW w0) where
  hom := ⟨(toNatTrans sq.inv).app (Functor.Fiber.fiberInclusion.obj w0), sorry⟩
  inv := ⟨(toNatTrans sq.hom).app (Functor.Fiber.fiberInclusion.obj w0), sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward component of `residueIso` is the fibrewise action of `sq.inv` on `w0`. -/
theorem residueIso_hom :
    Functor.Fiber.fiberInclusion.map (residueIso kToS fX gZ fW gW sq w0).hom =
      (toNatTrans sq.inv).app (Functor.Fiber.fiberInclusion.obj w0) :=
  sorry

/-- Natural transformation of total functors filling the image of a `2`-commutative
square of groupoid fibrations. -/
def mapCone_homNT :
    (map openImmersion h_factor fW w0).toFunctor ⋙
        (map openImmersion h_factor fX (residueImage fW w0)).toFunctor ⟶
      (map openImmersion h_factor gW w0).toFunctor ⋙
        mapFunctorAlong openImmersion kToS h_factor gZ
          (residueIso kToS fX gZ fW gW sq w0) where
  app ξ :=
    { baseHom := 𝟙 ξ.base
      hom := (toNatTrans sq.inv).app (Functor.Fiber.fiberInclusion.obj ξ.target)
      over_hom := sorry
      triangle := sorry }
  naturality := sorry

/-- Inverse natural transformation filling the image of a `2`-commutative square. -/
def mapCone_invNT :
    (map openImmersion h_factor gW w0).toFunctor ⋙
        mapFunctorAlong openImmersion kToS h_factor gZ
          (residueIso kToS fX gZ fW gW sq w0) ⟶
      (map openImmersion h_factor fW w0).toFunctor ⋙
        (map openImmersion h_factor fX (residueImage fW w0)).toFunctor where
  app ξ :=
    { baseHom := 𝟙 ξ.base
      hom := (toNatTrans sq.hom).app (Functor.Fiber.fiberInclusion.obj ξ.target)
      over_hom := sorry
      triangle := sorry }
  naturality := sorry

/-- Functor isomorphism filling the image of a `2`-commutative square. -/
def mapCone_functorIso :
    (map openImmersion h_factor fW w0).toFunctor ⋙
        (map openImmersion h_factor fX (residueImage fW w0)).toFunctor ≅
      (map openImmersion h_factor gW w0).toFunctor ⋙
        mapFunctorAlong openImmersion kToS h_factor gZ
          (residueIso kToS fX gZ fW gW sq w0) where
  hom := mapCone_homNT openImmersion kToS h_factor fX gZ fW gW sq w0
  inv := mapCone_invNT openImmersion kToS h_factor fX gZ fW gW sq w0
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Based-functor isomorphism filling the image of a `2`-commutative square. -/
def mapCone_iso :
    BasedFunctor.comp (map openImmersion h_factor fW w0)
        (map openImmersion h_factor fX (residueImage fW w0)) ≅
      BasedFunctor.comp (map openImmersion h_factor gW w0)
        (mapBasedFunctorAlong openImmersion kToS h_factor gZ
          (residueIso kToS fX gZ fW gW sq w0)) :=
  BasedNatIso.mkNatIso (mapCone_functorIso openImmersion kToS h_factor fX gZ fW gW sq w0) sorry

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
  sorry

/-- The canonical comparison from the constructed cone to the chosen two-fibre product of
the image cospan. -/
noncomputable def comparison :
    (mapCone openImmersion kToS h_factor fX gZ fW gW sq w0).pt ⟶
      (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
        (mapBundled openImmersion kToS h_factor fX (residueImage fW w0))
        (mapAlong openImmersion kToS h_factor gZ
          (residueIso kToS fX gZ fW gW sq w0))).pt :=
  Bicategory.PseudoPullbackCone.lift
    (mapCone openImmersion kToS h_factor fX gZ fW gW sq w0)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (mapBundled openImmersion kToS h_factor fX (residueImage fW w0))
      (mapAlong openImmersion kToS h_factor gZ
        (residueIso kToS fX gZ fW gW sq w0)))

/-- The comparison 1-morphism to the chosen two-fibre product of predeformation categories
is an equivalence over `ArtinianLocalAlgCat Λ k`, when the source square of groupoid
fibrations is a 2-fibre product. -/
theorem comparison_isEquivalence
    (hW : Bicategory.PseudoPullbackCone.IsBilimit
      (⟨W, fW, gW, sq⟩ : Bicategory.PseudoPullbackCone fX gZ)) :
    BasedFunctor.IsEquivalence
      (CofiberedCategoryOver.Groupoids.toBasedFunctor
        (comparison openImmersion kToS h_factor fX gZ fW gW sq w0)) :=
  sorry

end Square

end AlgebraicGeometry.GroupoidsOver.Predeformation
