/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.DeformationSituation
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.InSets.Forgetful
public import ReasLib.AlgebraicGeometry.GroupoidsOver.GlobalSections.BaseChange

/-!
# The global-sections functor and its associated category fibred in groupoids

The source functor sends `T/S` to the global sections `Γ(W_T, F_T)`. The associated
category fibred in groupoids over `Over (Spec (CommRingCat.of Λ))` is the discrete Grothendieck construction of
that set-valued presheaf, forgotten from sets to groupoids.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TypeCat
open AlgebraicGeometry
open FiberedCategoryOver
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.GlobalSections

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of Λ))
variable (F : W.Modules)

/-- The set-valued functor `T/S ↦ Γ(W_T, F_T)` on `(Sch/S)^{op}`. -/
def sectionsFunctor : (Over (Spec (CommRingCat.of Λ)))ᵒᵖ ⥤ Type u where
  obj T := (Γ(modulePullback w F T.unop, ⊤) : Type u)
  map {T T'} f := TypeCat.ofHom (sectionsRestrict w F f.unop)
  map_id T := congrArg TypeCat.ofHom (sectionsRestrict_id w F T.unop)
  map_comp f g := congrArg TypeCat.ofHom (sectionsRestrict_comp w F g.unop f.unop)

/-- Evaluating `sectionsFunctor` on `T` recovers the global sections of `F_T`. -/
theorem sectionsFunctor_obj (T : (Over (Spec (CommRingCat.of Λ)))ᵒᵖ) :
    (sectionsFunctor w F).obj T = Γ(modulePullback w F T.unop, ⊤) :=
  rfl

/-- `sectionsFunctor` acts on morphisms by restriction of global sections along base change. -/
theorem sectionsFunctor_map {T T' : (Over (Spec (CommRingCat.of Λ)))ᵒᵖ} (f : T ⟶ T') :
    (sectionsFunctor w F).map f = TypeCat.ofHom (sectionsRestrict w F f.unop) :=
  rfl

/-- The category fibred in groupoids associated to the global-sections functor. -/
def toGroupoids : GroupoidsOver (Spec (CommRingCat.of Λ)) :=
  (Sets.toGroupoids (Over (Spec (CommRingCat.of Λ)))).obj ((Sets.ofPresheaf (Over (Spec (CommRingCat.of Λ)))).obj (sectionsFunctor w F))

/-- The groupoid fibration of the global-sections functor is the discrete Grothendieck
construction of `sectionsFunctor`, forgotten to groupoids. -/
theorem toGroupoids_spec :
    toGroupoids w F =
      (Sets.toGroupoids (Over (Spec (CommRingCat.of Λ)))).obj
        ((Sets.ofPresheaf (Over (Spec (CommRingCat.of Λ)))).obj (sectionsFunctor w F)) :=
  rfl

/-- The projection of `toGroupoids` is the opposite category-of-elements projection of
`sectionsFunctor`. -/
theorem toGroupoids_p :
    (toGroupoids w F).p = ((Sets.ofPresheaf (Over (Spec (CommRingCat.of Λ)))).obj (sectionsFunctor w F)).p :=
  rfl

/-- A section over an affine spectrum determines an object of the discrete groupoid fibration. -/
def objectOverSpec {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ))
    (ha : a.MapsIntoAffineOpen) (x : Γ(modulePullback w F (Over.mk a), ⊤)) :
    ObjectOverSpec (toGroupoids w F) :=
  ObjectOverSpec.of A a ha (op ⟨op (Over.mk a), x⟩) rfl

/-- A fiber object over an affine spectrum determines its section by transport along its projection. -/
def sectionAt (ξ : ObjectOverSpec (toGroupoids w F)) :
    Γ(modulePullback w F (Over.mk ξ.toS), ⊤) :=
  Sets.ofPresheaf.fiberToValue (sectionsFunctor w F) (Over.mk ξ.toS) ξ.toFiber

/-- The section associated to the object constructed from a section is the original section. -/
theorem objectOverSpec_section {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ))
    (ha : a.MapsIntoAffineOpen) (x : Γ(modulePullback w F (Over.mk a), ⊤)) :
    sectionAt w F (objectOverSpec w F a ha x) = x := sorry

/-- A square-zero extension and a section define a deformation situation for the sections fibration. -/
def deformationSituation {A A' : Type u} [CommRing A] [CommRing A']
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ))
    (ha : a.MapsIntoAffineOpen)
    (a' : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of Λ))
    (π : A' →+* A) [hsq : π.IsSquareZeroExtension]
    (hπ : Spec.map (CommRingCat.ofHom π) ≫ a' = a)
    (x : Γ(modulePullback w F (Over.mk a), ⊤)) :
    DeformationSituation (toGroupoids w F) where
  toObjectOverSpec := objectOverSpec w F a ha x
  sourceRing := CommRingCat.of A'
  extension := ⟨π, hsq⟩
  sourceToS := a'
  toS_comp := hπ

end AlgebraicGeometry.GroupoidsOver.GlobalSections
