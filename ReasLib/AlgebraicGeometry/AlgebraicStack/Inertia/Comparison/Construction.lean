module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Naturality
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable

/-!
# Inertia comparison to a fibre product

The canonical 1-morphism `I_X ⟶ X ×_Y I_Y` associated to `f : X ⟶ Y` is the
universal lift of the inertia-forget/map cone into the chosen 2-fibre product
of `f` against `forget Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Inertia

/-- The 2-commutative square with apex `inertia X`, first leg `forget X`,
second leg `map f`, and cospan `X ⟶ Y ← I_Y`. -/
def comparisonCone {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    PseudoPullbackCone f (forget.{u + 1, u, u, u + 1} Y) where
  pt := inertia.{u + 1, u, u, u + 1} X
  fst := forget.{u + 1, u, u, u + 1} X
  snd := map.{u + 1, u, u, u + 1} f
  iso := eqToIso (map.comp_forget.{u + 1, u, u, u + 1} f).symm

/-- The apex of `comparisonCone f` is the inertia of `X`. -/
@[simp]
theorem comparisonCone_pt {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    (comparisonCone f).pt = inertia.{u + 1, u, u, u + 1} X :=
  sorry

/-- The first leg of `comparisonCone f` is `forget X`. -/
@[simp]
theorem comparisonCone_fst {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    (comparisonCone f).fst = forget.{u + 1, u, u, u + 1} X :=
  sorry

/-- The second leg of `comparisonCone f` is `map f`. -/
@[simp]
theorem comparisonCone_snd {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    (comparisonCone f).snd = map.{u + 1, u, u, u + 1} f :=
  sorry

/-- The comparison cell of `comparisonCone f` is the inverse of
`map.comp_forget f`. -/
@[simp]
theorem comparisonCone_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) :
    (comparisonCone f).iso =
      eqToIso (map.comp_forget.{u + 1, u, u, u + 1} f).symm :=
  sorry

/-- The canonical 1-morphism `I_X ⟶ X ×_Y I_Y` induced by `f`. -/
def comparison {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    inertia.{u + 1, u, u, u + 1} X ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} f
        (forget.{u + 1, u, u, u + 1} Y) :=
  PseudoPullbackCone.lift (comparisonCone f)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f
      (forget.{u + 1, u, u, u + 1} Y))

/-- `comparison f` is the universal lift of `comparisonCone f` into the chosen
2-fibre product of `f` against `forget Y`. -/
theorem comparison_eq {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    comparison f =
      PseudoPullbackCone.lift (comparisonCone f)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f
          (forget.{u + 1, u, u, u + 1} Y)) :=
  sorry

/-- After composing with the first projection, `comparison f` recovers
`forget X`. -/
def comparison_fstIso {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    comparison f ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} f
          (forget.{u + 1, u, u, u + 1} Y) ≅
      forget.{u + 1, u, u, u + 1} X :=
  PseudoPullbackCone.lift.fstIso (comparisonCone f)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f
      (forget.{u + 1, u, u, u + 1} Y))

/-- After composing with the second projection, `comparison f` recovers
`map f`. -/
def comparison_sndIso {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    comparison f ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u} f
          (forget.{u + 1, u, u, u + 1} Y) ≅
      map.{u + 1, u, u, u + 1} f :=
  PseudoPullbackCone.lift.sndIso (comparisonCone f)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} f
      (forget.{u + 1, u, u, u + 1} Y))

end AlgebraicGeometry.AlgebraicStack.Inertia
