module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Naturality
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Functoriality.Construction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Monomorphism

/-!
# Inertia squares of fully faithful morphisms

The canonical inertia-forget square of a fully faithful morphism of categories
fibred in groupoids is a 2-fibre product. In particular, this holds for a
monomorphism of algebraic stacks.
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
  rfl

/-- The first leg of `mapForgetCone f` is `Inertia.map f`. -/
@[simp]
theorem mapForgetCone_fst :
    (mapForgetCone f).fst = map.{u + 1, u, u, u + 1} f :=
  rfl

/-- The second leg of `mapForgetCone f` is `Inertia.forget X`. -/
@[simp]
theorem mapForgetCone_snd :
    (mapForgetCone f).snd = forget.{u + 1, u, u, u + 1} X :=
  rfl

/-- The comparison cell of `mapForgetCone f` is `mapForgetIso f`. -/
@[simp]
theorem mapForgetCone_iso : (mapForgetCone f).iso = mapForgetIso f :=
  rfl

/-- If `toBasedFunctor f` is fully faithful, then `mapForgetCone f` is a
2-fibre product. -/
theorem mapForgetCone.isBilimit_of_fullyFaithful
    (hf : Nonempty (toBasedFunctor f).FullyFaithful) :
    (mapForgetCone f).IsBilimit :=
  sorry

/-- The canonical inertia-forget square of a monomorphism of algebraic stacks
is a 2-fibre product. -/
instance mapForgetCone.isBilimit {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Mono f] :
    (mapForgetCone f).IsBilimit :=
  mapForgetCone.isBilimit_of_fullyFaithful f
    (AlgebraicGeometry.Groupoids.Hom.Mono.fullyFaithful f)

end AlgebraicGeometry.AlgebraicStack.Inertia
