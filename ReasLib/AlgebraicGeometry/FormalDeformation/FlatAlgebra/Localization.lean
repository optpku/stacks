module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.RingTheory.Localization.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra

/-!
# Localization functor of ring deformation categories

A multiplicative subset `S ⊆ P` induces a functor
`deformationCategory Λ k P ⥤ deformationCategory Λ k (Localization S)`
sending a deformation `(A, Q) → (k, P)` to `(A, S_Q⁻¹ Q) → (k, S⁻¹ P)`,
where `S_Q` is the inverse image of `S` in `Q`.
-/

@[expose] public section

open CategoryTheory Functor
open scoped BasedFunctor

universe u

namespace FlatAlgebraCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]

/-- The underlying ring map `Q →+* P` of a morphism `(A, Q) ⟶ (k, P)`. -/
def residueRingHom {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P) :
    Q.algebra →+* P :=
  f.toRingHom

/-- `residueRingHom` is the stored ring map of a morphism to `ofResidue P`. -/
theorem residueRingHom_apply {Q : FlatAlgebraCat Λ k} (f : Q ⟶ ofResidue Λ k P)
    (x : Q.algebra) : residueRingHom f x = f.toRingHom x :=
  rfl

/-- Inverse image `S_Q ⊆ Q` of a multiplicative subset `S ⊆ P` along a morphism
`(A, Q) ⟶ (k, P)` in `FlatAlgebraCat`. -/
abbrev preimageSubmonoid (S : Submonoid P) {Q : FlatAlgebraCat Λ k}
    (f : Q ⟶ ofResidue Λ k P) : Submonoid Q.algebra :=
  S.comap (residueRingHom f)

/-- Membership in `preimageSubmonoid` is inverse-image membership along `toRingHom`. -/
theorem preimageSubmonoid_mem (S : Submonoid P) {Q : FlatAlgebraCat Λ k}
    (f : Q ⟶ ofResidue Λ k P) {x : Q.algebra} :
    x ∈ preimageSubmonoid S f ↔ f.toRingHom x ∈ S :=
  Iff.rfl

/-- Localization of a flat algebra is flat over its base. -/
private theorem localizeObj_flat (S : Submonoid P) (X : deformationCategory Λ k P) :
    Module.Flat X.left.base.carrier (Localization (preimageSubmonoid S X.hom)) := sorry

/-- The localized pair `(A, S_Q⁻¹ Q)` of a deformation of `P`. -/
def localizeObj (S : Submonoid P) (X : deformationCategory Λ k P) : FlatAlgebraCat Λ k :=
  of X.left.base (Localization (preimageSubmonoid S X.hom))
    (isFlat := by exact localizeObj_flat S X)

/-- `localizeObj` keeps the Artinian base of the original deformation. -/
theorem localizeObj_base (S : Submonoid P) (X : deformationCategory Λ k P) :
    (localizeObj S X).base = X.left.base :=
  rfl

/-- The algebra of `localizeObj S X` is the localization of `Q` at `S_Q`. -/
theorem localizeObj_algebra (S : Submonoid P) (X : deformationCategory Λ k P) :
    (localizeObj S X).algebra = Localization (preimageSubmonoid S X.hom) :=
  rfl

/-- The localization map commutes with the base algebra maps. -/
private theorem localizeHom_commutes (S : Submonoid P) (X : deformationCategory Λ k P) :
    ((IsLocalization.map (Localization S) (residueRingHom X.hom)
      (le_rfl : preimageSubmonoid S X.hom ≤ S.comap (residueRingHom X.hom)) :
      Localization (preimageSubmonoid S X.hom) →+* Localization S)).comp (algebraMap (localizeObj S X).base.carrier (localizeObj S X).algebra) =
      (algebraMap (ofResidue Λ k (Localization S)).base.carrier (ofResidue Λ k (Localization S)).algebra).comp (X.hom.baseHom).hom.toRingHom := sorry

/-- The canonical tensor lift of the localization map is bijective. -/
private theorem localizeHom_isIsoTensor (S : Submonoid P) (X : deformationCategory Λ k P) :
    Function.Bijective (canonicalTensorMap
      (Q := localizeObj S X) (P := ofResidue Λ k (Localization S))
      (X.hom.baseHom) ((IsLocalization.map (Localization S) (residueRingHom X.hom)
      (le_rfl : preimageSubmonoid S X.hom ≤ S.comap (residueRingHom X.hom)) :
      Localization (preimageSubmonoid S X.hom) →+* Localization S)) (localizeHom_commutes S X)) := sorry

/-- The morphism `(A, S_Q⁻¹ Q) ⟶ (k, S⁻¹ P)` induced by localization. -/
noncomputable def localizeHom (S : Submonoid P) (X : deformationCategory Λ k P) :
    localizeObj S X ⟶ ofResidue Λ k (Localization S) :=
  Hom.of (X.hom.baseHom) ((IsLocalization.map (Localization S) (residueRingHom X.hom)
      (le_rfl : preimageSubmonoid S X.hom ≤ S.comap (residueRingHom X.hom)) :
      Localization (preimageSubmonoid S X.hom) →+* Localization S))
    (by exact localizeHom_commutes S X) (by exact localizeHom_isIsoTensor S X)

/-- `localizeHom` keeps the underlying morphism of Artinian local algebras. -/
theorem localizeHom_baseHom (S : Submonoid P) (X : deformationCategory Λ k P) :
    (localizeHom S X).baseHom = X.hom.baseHom :=
  rfl

/-- The localization map commutes with the base algebra maps. -/
private theorem localizeMap_commutes (S : Submonoid P) {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    ((IsLocalization.map (Localization (preimageSubmonoid S Y.hom)) f.left.toRingHom
      (le_of_eq
        (Eq.trans
          (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
            (congrArg Hom.toRingHom (Over.w f)).symm)
          (Eq.trans
            (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
              (rfl : (f.left ≫ Y.hom).toRingHom = Y.hom.toRingHom.comp f.left.toRingHom))
            (rfl :
              S.comap (Y.hom.toRingHom.comp f.left.toRingHom) =
                (preimageSubmonoid S Y.hom).comap f.left.toRingHom))) :
        preimageSubmonoid S X.hom ≤
          (preimageSubmonoid S Y.hom).comap f.left.toRingHom) :
      Localization (preimageSubmonoid S X.hom) →+*
        Localization (preimageSubmonoid S Y.hom))).comp (algebraMap (localizeObj S X).base.carrier (localizeObj S X).algebra) =
      (algebraMap (localizeObj S Y).base.carrier (localizeObj S Y).algebra).comp (f.left.baseHom).hom.toRingHom := sorry

/-- The canonical tensor lift of the localization map is bijective. -/
private theorem localizeMap_isIsoTensor (S : Submonoid P) {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    Function.Bijective (canonicalTensorMap
      (Q := localizeObj S X) (P := localizeObj S Y)
      (f.left.baseHom) ((IsLocalization.map (Localization (preimageSubmonoid S Y.hom)) f.left.toRingHom
      (le_of_eq
        (Eq.trans
          (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
            (congrArg Hom.toRingHom (Over.w f)).symm)
          (Eq.trans
            (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
              (rfl : (f.left ≫ Y.hom).toRingHom = Y.hom.toRingHom.comp f.left.toRingHom))
            (rfl :
              S.comap (Y.hom.toRingHom.comp f.left.toRingHom) =
                (preimageSubmonoid S Y.hom).comap f.left.toRingHom))) :
        preimageSubmonoid S X.hom ≤
          (preimageSubmonoid S Y.hom).comap f.left.toRingHom) :
      Localization (preimageSubmonoid S X.hom) →+*
        Localization (preimageSubmonoid S Y.hom))) (localizeMap_commutes S f)) := sorry

/-- The morphism of localized pairs induced by a morphism of deformations. -/
noncomputable def localizeMap (S : Submonoid P) {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    localizeObj S X ⟶ localizeObj S Y :=
  Hom.of (f.left.baseHom) ((IsLocalization.map (Localization (preimageSubmonoid S Y.hom)) f.left.toRingHom
      (le_of_eq
        (Eq.trans
          (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
            (congrArg Hom.toRingHom (Over.w f)).symm)
          (Eq.trans
            (congrArg (fun φ : X.left.algebra →+* P ↦ S.comap φ)
              (rfl : (f.left ≫ Y.hom).toRingHom = Y.hom.toRingHom.comp f.left.toRingHom))
            (rfl :
              S.comap (Y.hom.toRingHom.comp f.left.toRingHom) =
                (preimageSubmonoid S Y.hom).comap f.left.toRingHom))) :
        preimageSubmonoid S X.hom ≤
          (preimageSubmonoid S Y.hom).comap f.left.toRingHom) :
      Localization (preimageSubmonoid S X.hom) →+*
        Localization (preimageSubmonoid S Y.hom)))
    (by exact localizeMap_commutes S f) (by exact localizeMap_isIsoTensor S f)

/-- `localizeMap` keeps the underlying morphism of Artinian local algebras. -/
theorem localizeMap_baseHom (S : Submonoid P) {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    (localizeMap S f).baseHom = f.left.baseHom :=
  rfl

/-- Localized maps commute with the maps to the localized residue algebra. -/
private theorem localizeMap_w (S : Submonoid P) {X Y : deformationCategory Λ k P}
    (f : X ⟶ Y) : localizeMap S f ≫ localizeHom S Y = localizeHom S X := sorry

/-- Localization preserves identity maps of deformations. -/
private theorem localizeMap_id (S : Submonoid P) (X : deformationCategory Λ k P) :
    localizeMap S (𝟙 X) = 𝟙 (localizeObj S X) := sorry

/-- Localization preserves composites of deformation maps. -/
private theorem localizeMap_comp (S : Submonoid P) {X Y Z : deformationCategory Λ k P}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    localizeMap S (f ≫ g) = localizeMap S f ≫ localizeMap S g := sorry

/-- The functor `Def_P ⥤ Def_{S⁻¹ P}` sending a deformation of `P` to its localization at `S`. -/
noncomputable def localizationFunctor (S : Submonoid P) :
    deformationCategory Λ k P ⥤ deformationCategory Λ k (Localization S) where
  obj X := Over.mk (localizeHom S X)
  map f := Over.homMk (localizeMap S f) (by exact localizeMap_w S f)
  map_id X := by
    apply Over.OverMorphism.ext
    exact localizeMap_id S X
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact localizeMap_comp S f g

/-- The localized deformation has the same Artinian base. -/
theorem localizationFunctor_obj_base (S : Submonoid P) (X : deformationCategory Λ k P) :
    ((localizationFunctor S).obj X).left.base = X.left.base :=
  rfl

/-- The localized deformation has algebra `S_Q⁻¹ Q`. -/
theorem localizationFunctor_obj_algebra (S : Submonoid P) (X : deformationCategory Λ k P) :
    ((localizationFunctor S).obj X).left.algebra =
      Localization (preimageSubmonoid S X.hom) :=
  rfl

/-- `localizationFunctor` lies over `C_Λ`: it commutes with the projections to
`ArtinianLocalAlgCat`. -/
theorem localizationFunctor_comp_forget (S : Submonoid P) :
    localizationFunctor S ⋙
        Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k (Localization S))) ⋙ forget =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget :=
  sorry

section

variable (Λ k)

/-- The localization functor as a morphism of categories over `C_Λ`. -/
noncomputable def localizationBasedFunctor (S : Submonoid P) :
    BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙
          (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)) ⥤ᵇ
      BasedCategory.ofFunctor
        (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k (Localization S))) ⋙
          (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)) where
  toFunctor := localizationFunctor S
  w := localizationFunctor_comp_forget S

/-- The underlying functor of `localizationBasedFunctor` is `localizationFunctor`. -/
theorem localizationBasedFunctor_toFunctor (S : Submonoid P) :
    (localizationBasedFunctor Λ k S).toFunctor = localizationFunctor S :=
  rfl

end

end FlatAlgebraCat
