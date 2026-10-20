/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Limits of commutative algebras

For a diagram `F : J ⥤ CommAlgCat.{w} R` with `UnivLE.{v, w}` (the object universe of `J`
bounded by the algebra universe), the limit is the subalgebra of compatible families in
`∀ j, F.obj j`, shrunk to universe `w`; the cone maps are the evaluations and the universal map
is the tuple of cone components.  The same carrier is a limit of the underlying commutative
rings, so the forgetful functor to `CommRingCat` preserves these limits.

Mathlib's same-universe `HasLimits (CommAlgCat.{u} R)` (via `commAlgCatEquivUnder`) stays
canonical; the universe-polymorphic instances here have lower priority.  This file does not
depend on any site or sheaf construction.
-/

@[expose] public section

noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

variable {R : Type u} [CommRing R]
section Construction

variable {J : Type v} [Category.{t} J] (F : J ⥤ CommAlgCat.{w} R)

/-- The compatible families of a diagram of commutative algebras, as a subalgebra of the
product of its values. -/
def sectionsSubalgebra : Subalgebra R (∀ j, F.obj j) where
  carrier := {x | ∀ ⦃i j : J⦄ (f : i ⟶ j), F.map f (x i) = x j}
  mul_mem' {x y} hx hy i j f := by simp [hx f, hy f]
  add_mem' {x y} hx hy i j f := by simp [hx f, hy f]
  algebraMap_mem' r i j f := by simp

lemma mem_sectionsSubalgebra {x : ∀ j, F.obj j} :
    x ∈ sectionsSubalgebra F ↔ ∀ ⦃i j : J⦄ (f : i ⟶ j), F.map f (x i) = x j :=
  Iff.rfl

variable [UnivLE.{v, w}]

namespace HasLimits

/-- The limit cone of a diagram of commutative algebras: the compatible families, shrunk to the
algebra universe, with the evaluation maps.  (Internal; use the limits API.) -/
def limitCone : Cone F where
  pt := CommAlgCat.of R (Shrink.{w} (sectionsSubalgebra F))
  π :=
    { app := fun j ↦ ofHom <| (Pi.evalAlgHom R (fun j ↦ F.obj j) j).comp
        ((sectionsSubalgebra F).val.comp (Shrink.algEquiv R (sectionsSubalgebra F)).toAlgHom)
      naturality := fun i j f ↦ by
        ext x
        exact ((Shrink.algEquiv R (sectionsSubalgebra F) x).2 f).symm }

lemma limitCone_π_app_apply (j : J) (x : Shrink.{w} (sectionsSubalgebra F)) :
    (limitCone F).π.app j x = (Shrink.algEquiv R (sectionsSubalgebra F) x).1 j :=
  rfl

/-- The compatible family of the components of a cone over a diagram of commutative algebras. -/
def liftToSections (s : Cone F) : s.pt →ₐ[R] sectionsSubalgebra F :=
  let g : s.pt →ₐ[R] ∀ j, F.obj j := AlgHom.pi fun j ↦ (s.π.app j).hom
  g.codRestrict (sectionsSubalgebra F) fun x _ _ f ↦ ConcreteCategory.congr_hom (s.w f) x

/-- The universal map from a cone over a diagram of commutative algebras to the chosen limit. -/
def liftAlgHom (s : Cone F) : s.pt →ₐ[R] Shrink.{w} (sectionsSubalgebra F) :=
  (Shrink.algEquiv R (sectionsSubalgebra F)).symm.toAlgHom.comp (liftToSections F s)

lemma algEquiv_liftAlgHom (s : Cone F) (x : s.pt) (j : J) :
    (Shrink.algEquiv R (sectionsSubalgebra F) (liftAlgHom F s x)).1 j = s.π.app j x :=
  show (fun y : sectionsSubalgebra F ↦ (y : ∀ j, F.obj j) j) _ = _ from congrArg (fun y : sectionsSubalgebra F ↦ (y : ∀ j, F.obj j) j)
    ((Shrink.algEquiv R (sectionsSubalgebra F)).apply_symm_apply (liftToSections F s x))

/-- The chosen cone is a limit cone.  (Internal; use the limits API.) -/
def limitConeIsLimit : IsLimit (limitCone F) where
  lift s := ofHom (liftAlgHom F s)
  fac s j := by
    ext x
    exact algEquiv_liftAlgHom F s x j
  uniq s m hm := by
    ext x
    apply (Shrink.algEquiv R (sectionsSubalgebra F)).injective
    apply Subtype.ext
    funext j
    exact (ConcreteCategory.congr_hom (hm j) x).trans (algEquiv_liftAlgHom F s x j).symm

/-- The compatible family of the components of a cone of commutative rings over the underlying
diagram of a diagram of commutative algebras. -/
def liftToSectionsRingHom (s : Cone (F ⋙ forget₂ (CommAlgCat.{w} R) CommRingCat.{w})) :
    s.pt →+* sectionsSubalgebra F :=
  let g : s.pt →+* ∀ j, F.obj j := RingHom.pi fun j ↦ (s.π.app j).hom
  g.codRestrict (sectionsSubalgebra F) fun x _ _ f ↦ ConcreteCategory.congr_hom (s.w f) x

/-- The universal ring map from a cone of commutative rings over the underlying diagram to the
underlying ring of the chosen limit. -/
def liftRingHom (s : Cone (F ⋙ forget₂ (CommAlgCat.{w} R) CommRingCat.{w})) :
    s.pt →+* Shrink.{w} (sectionsSubalgebra F) :=
  (Shrink.algEquiv R (sectionsSubalgebra F)).symm.toRingEquiv.toRingHom.comp
    (liftToSectionsRingHom F s)

lemma algEquiv_liftRingHom (s : Cone (F ⋙ forget₂ (CommAlgCat.{w} R) CommRingCat.{w}))
    (x : s.pt) (j : J) :
    (Shrink.algEquiv R (sectionsSubalgebra F) (liftRingHom F s x)).1 j = s.π.app j x :=
  show (fun y : sectionsSubalgebra F ↦ (y : ∀ j, F.obj j) j) _ = _ from congrArg (fun y : sectionsSubalgebra F ↦ (y : ∀ j, F.obj j) j)
    ((Shrink.algEquiv R (sectionsSubalgebra F)).apply_symm_apply (liftToSectionsRingHom F s x))

/-- The underlying cone of commutative rings of the chosen limit cone is a limit cone. -/
def forget₂CommRingLimitConeIsLimit :
    IsLimit ((forget₂ (CommAlgCat.{w} R) CommRingCat.{w}).mapCone (limitCone F)) where
  lift s := CommRingCat.ofHom (liftRingHom F s)
  fac s j := by
    ext x
    exact algEquiv_liftRingHom F s x j
  uniq s m hm := by
    ext x
    apply (Shrink.algEquiv R (sectionsSubalgebra F)).injective
    apply Subtype.ext
    funext j
    exact (ConcreteCategory.congr_hom (hm j) x).trans (algEquiv_liftRingHom F s x j).symm

end HasLimits

end Construction

open HasLimits

/-- The category of commutative algebras has limits when its universe bounds the indexing
category's object universe. -/
theorem hasLimitsOfSize_of_univLE [UnivLE.{v, w}] :
    HasLimitsOfSize.{t, v} (CommAlgCat.{w} R) :=
  { has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := limitCone F
          isLimit := limitConeIsLimit F } } }

/-- The category of commutative `R`-algebras has limits indexed by every category whose object
universe is bounded by the algebra universe.  The lower priority leaves mathlib's same-universe
instance canonical when both apply. -/
@[stacks 0CS6 "limits of commutative algebras"]
instance (priority := 90) hasLimitsOfSize [UnivLE.{v, w}] :
    HasLimitsOfSize.{t, v} (CommAlgCat.{w} R) :=
  hasLimitsOfSize_of_univLE

/-- The forgetful functor from commutative algebras to commutative rings preserves limits when
the algebra universe bounds the indexing category's object universe. -/
theorem forgetToCommRing_preservesLimitsOfSize_of_univLE [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v}
      (forget₂ (CommAlgCat.{w} R) CommRingCat.{w}) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (forget₂CommRingLimitConeIsLimit K) }

/-- The forgetful functor from commutative `R`-algebras to commutative rings preserves limits of
every size bounded by the algebra universe. -/
@[stacks 0CS6 "limits of underlying rings of commutative algebras"]
instance forget₂CommRing_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v}
      (forget₂ (CommAlgCat.{w} R) CommRingCat.{w}) :=
  forgetToCommRing_preservesLimitsOfSize_of_univLE

end CommAlgCat
