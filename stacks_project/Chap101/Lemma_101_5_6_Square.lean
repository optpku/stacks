/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Naturality
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Functoriality.Construction
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Inertia-forget square of a 1-morphism of groupoid fibrations

A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids determines a
2-commutative square with vertices `I_X`, `X`, `I_Y`, and `Y`.
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

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)

/-- The invertible 2-cell of the inertia-forget square, obtained from
`map.comp_forget`. -/
def mapForgetIso :
    map.{u + 1, u, u, u + 1} f ≫ forget.{u + 1, u, u, u + 1} Y ≅
      forget.{u + 1, u, u, u + 1} X ≫ f :=
  eqToIso (map.comp_forget.{u + 1, u, u, u + 1} f)

/-- The canonical 2-commutative square with apex `inertia X`, first leg
`Inertia.map f : I_X ⟶ I_Y`, and second leg `Inertia.forget X : I_X ⟶ X`. -/
def mapForgetCone :
    PseudoPullbackCone (forget.{u + 1, u, u, u + 1} Y) f where
  pt := inertia X
  fst := map.{u + 1, u, u, u + 1} f
  snd := forget.{u + 1, u, u, u + 1} X
  iso := mapForgetIso f

/-- The apex of `mapForgetCone f` is the inertia of `X`. -/
@[simp]
theorem mapForgetCone_pt : (mapForgetCone f).pt = inertia X :=
  sorry

/-- The first leg of `mapForgetCone f` is `Inertia.map f`. -/
@[simp]
theorem mapForgetCone_fst :
    (mapForgetCone f).fst = map.{u + 1, u, u, u + 1} f :=
  sorry

/-- The second leg of `mapForgetCone f` is `Inertia.forget X`. -/
@[simp]
theorem mapForgetCone_snd :
    (mapForgetCone f).snd = forget.{u + 1, u, u, u + 1} X :=
  sorry

/-- The comparison cell of `mapForgetCone f` is `mapForgetIso f`. -/
@[simp]
theorem mapForgetCone_iso : (mapForgetCone f).iso = mapForgetIso f :=
  sorry

/-- If `toBasedFunctor f` is fully faithful, then `mapForgetCone f` is a
2-fibre product. -/
theorem mapForgetCone.isBilimit_of_fullyFaithful
    (hf : Nonempty (toBasedFunctor f).FullyFaithful) :
    (mapForgetCone f).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Inertia
