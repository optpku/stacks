/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.RingTheory.Localization.Defs
public import stacks_project.Chap93.Example_93_8_1_Rings_Category

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
  sorry

/-- Inverse image `S_Q ⊆ Q` of a multiplicative subset `S ⊆ P` along a morphism
`(A, Q) ⟶ (k, P)` in `FlatAlgebraCat`. -/
abbrev preimageSubmonoid (S : Submonoid P) {Q : FlatAlgebraCat Λ k}
    (f : Q ⟶ ofResidue Λ k P) : Submonoid Q.algebra :=
  S.comap (residueRingHom f)

/-- Membership in `preimageSubmonoid` is inverse-image membership along `toRingHom`. -/
theorem preimageSubmonoid_mem (S : Submonoid P) {Q : FlatAlgebraCat Λ k}
    (f : Q ⟶ ofResidue Λ k P) {x : Q.algebra} :
    x ∈ preimageSubmonoid S f ↔ f.toRingHom x ∈ S :=
  sorry

/-- The localized pair `(A, S_Q⁻¹ Q)` of a deformation of `P`. -/
def localizeObj (S : Submonoid P) (X : deformationCategory Λ k P) : FlatAlgebraCat Λ k where
  base := X.left.base
  algebra := Localization (preimageSubmonoid S X.hom)
  isAlgebra :=
    Algebra.compHom (Localization (preimageSubmonoid S X.hom))
      (algebraMap X.left.base.carrier X.left.algebra)
  isFlat := sorry

/-- `localizeObj` keeps the Artinian base of the original deformation. -/
theorem localizeObj_base (S : Submonoid P) (X : deformationCategory Λ k P) :
    (localizeObj S X).base = X.left.base :=
  sorry

/-- The algebra of `localizeObj S X` is the localization of `Q` at `S_Q`. -/
theorem localizeObj_algebra (S : Submonoid P) (X : deformationCategory Λ k P) :
    (localizeObj S X).algebra = Localization (preimageSubmonoid S X.hom) :=
  sorry

/-- The morphism `(A, S_Q⁻¹ Q) ⟶ (k, S⁻¹ P)` induced by localizing `(A, Q) ⟶ (k, P)`. -/
noncomputable def localizeHom (S : Submonoid P) (X : deformationCategory Λ k P) :
    Hom (localizeObj S X) (ofResidue Λ k (Localization S)) where
  baseHom := X.hom.baseHom
  toRingHom :=
    (IsLocalization.map (Localization S) (residueRingHom X.hom)
      (le_rfl : preimageSubmonoid S X.hom ≤ S.comap (residueRingHom X.hom)) :
      Localization (preimageSubmonoid S X.hom) →+* Localization S)
  commutes := sorry
  isIso_tensor := sorry

/-- `localizeHom` keeps the underlying morphism of Artinian local algebras. -/
theorem localizeHom_baseHom (S : Submonoid P) (X : deformationCategory Λ k P) :
    (localizeHom S X).baseHom = X.hom.baseHom :=
  sorry

/-- The localized morphism of pairs induced by a morphism of deformations of `P`. -/
noncomputable def localizeMap (S : Submonoid P) {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    Hom (localizeObj S X) (localizeObj S Y) where
  baseHom := f.left.baseHom
  toRingHom :=
    (IsLocalization.map (Localization (preimageSubmonoid S Y.hom)) f.left.toRingHom
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
        Localization (preimageSubmonoid S Y.hom))
  commutes := sorry
  isIso_tensor := sorry

/-- `localizeMap` keeps the underlying morphism of Artinian local algebras. -/
theorem localizeMap_baseHom (S : Submonoid P) {X Y : deformationCategory Λ k P} (f : X ⟶ Y) :
    (localizeMap S f).baseHom = f.left.baseHom :=
  sorry

/-- The functor `Def_P ⥤ Def_{S⁻¹ P}` sending a deformation of `P` to its localization at `S`. -/
noncomputable def localizationFunctor (S : Submonoid P) :
    deformationCategory Λ k P ⥤ deformationCategory Λ k (Localization S) where
  obj X := Over.mk (localizeHom S X)
  map f := Over.homMk (localizeMap S f) sorry
  map_id := sorry
  map_comp := sorry

/-- The localized deformation has the same Artinian base. -/
theorem localizationFunctor_obj_base (S : Submonoid P) (X : deformationCategory Λ k P) :
    ((localizationFunctor S).obj X).left.base = X.left.base :=
  sorry

/-- The localized deformation has algebra `S_Q⁻¹ Q`. -/
theorem localizationFunctor_obj_algebra (S : Submonoid P) (X : deformationCategory Λ k P) :
    ((localizationFunctor S).obj X).left.algebra =
      Localization (preimageSubmonoid S X.hom) :=
  sorry

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
  w := sorry

/-- The underlying functor of `localizationBasedFunctor` is `localizationFunctor`. -/
theorem localizationBasedFunctor_toFunctor (S : Submonoid P) :
    (localizationBasedFunctor Λ k S).toFunctor = localizationFunctor S :=
  sorry

end

end FlatAlgebraCat
