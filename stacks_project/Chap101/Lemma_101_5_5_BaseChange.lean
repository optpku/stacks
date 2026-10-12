/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.RelativeFunctoriality.Stable.Naturality
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Relative inertia of a 2-fibre product of groupoid fibrations

The canonical left square of a relative-inertia base change, packaged as a
`PseudoPullbackCone` whose apex is `relativeInertia` of the second projection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.RelativeInertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeInertia

/-- The invertible 2-cell of the relative-inertia base-change square, obtained
from `map.comp_forget` along Categories Equation 04Z4 with
`comm = (TwoFibreProduct.comparisonIso π f).symm`. -/
def baseChangeIso {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    (π : X ⟶ Y) (f : Y' ⟶ Y) :
    map.{u + 1, u, u, u + 1}
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} π f) f
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} π f).symm ≫
      forget.{u + 1, u, u, u + 1} π ≅
      forget.{u + 1, u, u, u + 1}
          (TwoFibreProduct.snd.{u + 1, u, u + 1, u} π f) ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} π f :=
  eqToIso
    (map.comp_forget.{u + 1, u, u, u + 1}
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} π f) f
      (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} π f).symm)

/-- The canonical 2-commutative square with apex
`relativeInertia (TwoFibreProduct.snd π f)`, first leg the 04Z4 map
from relative inertia of the base-changed morphism, and second leg `forget`
of that morphism. -/
def baseChangeCone {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    (π : X ⟶ Y) (f : Y' ⟶ Y) :
    PseudoPullbackCone (forget.{u + 1, u, u, u + 1} π)
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} π f) where
  pt := relativeInertia.{u + 1, u, u, u + 1}
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} π f)
  fst := map.{u + 1, u, u, u + 1}
    (TwoFibreProduct.fst.{u + 1, u, u + 1, u} π f) f
    (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} π f).symm
  snd := forget.{u + 1, u, u, u + 1}
    (TwoFibreProduct.snd.{u + 1, u, u + 1, u} π f)
  iso := baseChangeIso π f

/-- The apex of `baseChangeCone π f` is relative inertia of the second
projection `TwoFibreProduct.snd π f`. -/
@[simp]
theorem baseChangeCone_pt {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    (π : X ⟶ Y) (f : Y' ⟶ Y) :
    (baseChangeCone π f).pt =
      relativeInertia.{u + 1, u, u, u + 1}
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} π f) :=
  sorry

/-- The first leg of `baseChangeCone π f` is the relative-inertia map of
Categories Equation 04Z4. -/
@[simp]
theorem baseChangeCone_fst {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    (π : X ⟶ Y) (f : Y' ⟶ Y) :
    (baseChangeCone π f).fst =
      map.{u + 1, u, u, u + 1}
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} π f) f
        (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} π f).symm :=
  sorry

/-- The second leg of `baseChangeCone π f` is `forget` of the base-changed
morphism `TwoFibreProduct.snd π f`. -/
@[simp]
theorem baseChangeCone_snd {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    (π : X ⟶ Y) (f : Y' ⟶ Y) :
    (baseChangeCone π f).snd =
      forget.{u + 1, u, u, u + 1}
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} π f) :=
  sorry

/-- The comparison cell of `baseChangeCone π f` is `baseChangeIso π f`. -/
@[simp]
theorem baseChangeCone_iso {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    (π : X ⟶ Y) (f : Y' ⟶ Y) :
    (baseChangeCone π f).iso = baseChangeIso π f :=
  sorry

/-- The relative-inertia base-change square is a 2-fibre product. -/
instance baseChangeCone.isBilimit {S : Scheme.{u}} {X Y Y' : GroupoidsOver S}
    (π : X ⟶ Y) (f : Y' ⟶ Y) :
    (baseChangeCone π f).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeInertia

