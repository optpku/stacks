/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

@[expose] public section

noncomputable section

open CategoryTheory.Limits

universe u v u' v'

namespace CategoryTheory.InjectiveResolution.ExactMap

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
variable {X : A} (I : InjectiveResolution X) (J : InjectiveResolution (L.obj X))

set_option backward.privateInPublic true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmentation of the target resolution extends across the mapped source augmentation. -/
private def zero : L.obj (I.cocomplex.X 0) ⟶ J.cocomplex.X 0 :=
  Injective.factorThru (J.ι.f 0) (L.map (I.ι.f 0))

set_option backward.privateInPublic true in
/-- The extended augmentation annihilates the first target differential after restriction. -/
theorem zeroCondition :
    L.map (I.ι.f 0) ≫ (zero L I J ≫ J.cocomplex.d 0 1) = 0 := sorry

set_option backward.privateInPublic true in
/-- Exactness extends the degree-zero comparison to degree one. -/
private def one : L.obj (I.cocomplex.X 1) ⟶ J.cocomplex.X 1 :=
  (I.exact₀.map L).descToInjective (zero L I J ≫ J.cocomplex.d 0 1)
    (zeroCondition L I J)

/-- Two consecutive commuting components annihilate the next target differential. -/
theorem stepCondition (degree : ℕ)
    (first : L.obj (I.cocomplex.X degree) ⟶ J.cocomplex.X degree)
    (second : L.obj (I.cocomplex.X (degree + 1)) ⟶ J.cocomplex.X (degree + 1))
    (comm : first ≫ J.cocomplex.d degree (degree + 1) =
      L.map (I.cocomplex.d degree (degree + 1)) ≫ second) :
    L.map (I.cocomplex.d degree (degree + 1)) ≫
      (second ≫ J.cocomplex.d (degree + 1) (degree + 2)) = 0 := sorry

set_option backward.privateInPublic true in
/-- An exact additive image of a resolution admits a comparison to an injective resolution
of the image object, without requiring the image terms to be injective. -/
def map : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex :=
  CochainComplex.mkHom _ _ (zero L I J) (one L I J)
    ((I.exact₀.map L).comp_descToInjective
      (zero L I J ≫ J.cocomplex.d 0 1) (zeroCondition L I J)).symm
    (fun degree components =>
      ⟨(I.exact_succ degree |>.map L).descToInjective
          (components.2.1 ≫ J.cocomplex.d (degree + 1) (degree + 2))
          (stepCondition L I J degree components.1 components.2.1 components.2.2),
        ((I.exact_succ degree |>.map L).comp_descToInjective
          (components.2.1 ≫ J.cocomplex.d (degree + 1) (degree + 2))
          (stepCondition L I J degree components.1 components.2.1 components.2.2)).symm⟩)

/-- The comparison intertwines the mapped augmentation with the target augmentation. -/
theorem map_ι : L.map (I.ι.f 0) ≫ (map L I J).f 0 = J.ι.f 0 := sorry

end CategoryTheory.InjectiveResolution.ExactMap
