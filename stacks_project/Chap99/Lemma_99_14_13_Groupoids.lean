/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap99.Situation_99_14_1

/-!
# Polarized as a category fibred in groupoids over a scheme

The costructured-arrow category of Polarized over a scheme `S` is packaged as
an object of `GroupoidsOver S`, recovering scheme-level base change of
Polarized.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The forgetful functor of scheme-level `S`-Polarized, sending a polarized
object equipped with a morphism from its base scheme into `S` to that morphism
as an object of `Over S`. -/
def pOver (S : Scheme.{u}) : CostructuredArrow p S ⥤ Over S where
  obj x := Over.mk x.hom
  map f := Over.homMk (p.map f.left) (CostructuredArrow.w f)
  map_id := sorry
  map_comp := sorry

/-- The object map of `pOver S` is `Over.mk` of the costructured-arrow morphism
to `S`. -/
theorem pOver_obj (S : Scheme.{u}) (x : CostructuredArrow p S) :
    (pOver S).obj x = Over.mk x.hom :=
  sorry

/-- The morphism map of `pOver S` is `Over.homMk` of the image of the underlying
Polarized morphism under `p`. -/
theorem pOver_map {S : Scheme.{u}} {x y : CostructuredArrow p S} (f : x ⟶ y) :
    (pOver S).map f = Over.homMk (p.map f.left) (CostructuredArrow.w f) :=
  sorry

/-- The forgetful functor of scheme-level `S`-Polarized is fibred in groupoids. -/
instance instIsFiberedInGroupoids_pOver (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids (pOver S) :=
  sorry

/-- Polarized, bundled as a category fibred in groupoids over `(Sch / S)_fppf`. -/
def toGroupoidsOver (S : Scheme.{u}) : GroupoidsOver S :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u} (pOver S)

/-- The projection of `toGroupoidsOver S` is `pOver S`. -/
theorem toGroupoidsOver_p (S : Scheme.{u}) :
    (toGroupoidsOver S).p = pOver S :=
  sorry

/-- `toGroupoidsOver S` is the groupoid fibration associated to `pOver S`. -/
theorem toGroupoidsOver_spec (S : Scheme.{u}) :
    toGroupoidsOver S =
      FiberedCategoryOver.Groupoids.ofFunctor (pOver S) :=
  sorry

end AlgebraicGeometry.Polarized
