/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import ReasLib.AlgebraicGeometry.GroupoidsOver.CompleteLocalObject
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Category

/-! # Approximation by maximal-adic restrictions

Cartesian restriction along the positive maximal-adic quotients defines a functor
from complete local objects with local morphisms to formal objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

namespace FormalObject

variable {X : GroupoidsOver S}

/-- Restriction of an object along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restrictionObj (x : CompleteLocalObject X) (n : ℕ) : X.total :=
  IsPreFibered.pullbackObj x.over_obj (x.base.truncationOverHom n)

/-- Cartesian lift of restriction along `Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restrictionHom (x : CompleteLocalObject X) (n : ℕ) :
    restrictionObj x n ⟶ x.object :=
  IsPreFibered.pullbackMap x.over_obj (x.base.truncationOverHom n)

/-- Restriction of `x` to stage `n` is cartesian over `truncationOverHom`. -/
theorem restrictionHom_isCartesian (x : CompleteLocalObject X) (n : ℕ) :
    X.p.IsCartesian (x.base.truncationOverHom n) (restrictionHom x n) :=
  IsPreFibered.pullbackMap.IsCartesian x.over_obj (x.base.truncationOverHom n)

/-- Restriction of `x` to stage `n` is strongly cartesian. -/
theorem restrictionHom_isStronglyCartesian (x : CompleteLocalObject X) (n : ℕ) :
    X.p.IsStronglyCartesian (x.base.truncationOverHom n) (restrictionHom x n) :=
  @IsFibered.isStronglyCartesian_of_isCartesian _ _ _ _ X.p inferInstance _ _
    (x.base.truncationOverHom n) _ _ (restrictionHom x n) (restrictionHom_isCartesian x n)

/-- Stage `n` of the restricted system lies over `Spec(R ⧸ m^{n+1})`. -/
theorem restrictionObj_over (x : CompleteLocalObject X) (n : ℕ) :
    X.p.obj (restrictionObj x n) = x.base.stageOver n :=
  IsPreFibered.pullbackObj_proj x.over_obj (x.base.truncationOverHom n)

/-- Successor comparison between chosen maximal-adic restrictions. -/
def restrictionStep (x : CompleteLocalObject X) (n : ℕ) :
    restrictionObj x n ⟶ restrictionObj x (n + 1) :=
  @IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _
    (x.base.truncationOverHom (n + 1)) (restrictionHom x (n + 1))
    (restrictionHom_isStronglyCartesian x (n + 1)) _ _ _ _
    (x.base.truncationOverHom_comp n) (restrictionHom x n)
    (restrictionHom_isCartesian x n).toIsHomLift

/-- Successor comparisons lift the canonical maps of truncated spectra. -/
theorem restrictionStep_isHomLift (x : CompleteLocalObject X) (n : ℕ) :
    X.p.IsHomLift (x.base.stageHom n) (restrictionStep x n) :=
  @IsStronglyCartesian.map_isHomLift _ _ _ _ X.p _ _ _ _
    (x.base.truncationOverHom (n + 1)) (restrictionHom x (n + 1))
    (restrictionHom_isStronglyCartesian x (n + 1)) _ _ _ _
    (x.base.truncationOverHom_comp n) (restrictionHom x n)
    (restrictionHom_isCartesian x n).toIsHomLift

/-- Formal object obtained by restricting `x` along all truncations
`Spec(R ⧸ m^{n+1}) ⟶ Spec(R)`. -/
def restriction (x : CompleteLocalObject X) : FormalObject X :=
  of x.base (restrictionObj x) (restrictionStep x)
    (fun n ↦ IsPreFibered.pullbackObj_proj x.over_obj (x.base.truncationOverHom n))
    (restrictionStep_isHomLift x)

/-- Stage objects of `restriction x` are the chosen cartesian restrictions. -/
theorem restriction_family (x : CompleteLocalObject X) (n : ℕ) :
    (restriction x).objects n = restrictionObj x n := rfl

/-- Successor maps of `restriction x` are the transitivity comparisons. -/
theorem restriction_step (x : CompleteLocalObject X) (n : ℕ) :
    (restriction x).step n = restrictionStep x n := rfl

/-- Restriction followed by a local arrow factors through the induced truncated base map. -/
theorem approximation_factor {x y : CompleteLocalObject X} (f : CompleteLocalObject.Hom x y)
    (n : ℕ) :
    x.base.truncationOverHom n ≫ CompleteLocalObject.overHom f.hom =
      (CompleteLocalObject.baseHom f).stageMap n ≫ y.base.truncationOverHom n := sorry

/-- The restricted composite lifts the corresponding composite of base maps. -/
theorem approximationApp_isHomLift {x y : CompleteLocalObject X}
    (f : CompleteLocalObject.Hom x y) (n : ℕ) :
    X.p.IsHomLift (x.base.truncationOverHom n ≫ CompleteLocalObject.overHom f.hom)
      (restrictionHom x n ≫ f.hom) :=
  @IsHomLift.comp _ _ _ _ X.p _ _ _ _ _ _ (x.base.truncationOverHom n)
    (CompleteLocalObject.overHom f.hom) (restrictionHom x n) f.hom
    (restrictionHom_isCartesian x n).toIsHomLift
    (CompleteLocalObject.overHom_isHomLift f.hom)

/-- Restrict a local morphism at a positive maximal-adic stage by cartesian factorization. -/
def approximationApp {x y : CompleteLocalObject X} (f : CompleteLocalObject.Hom x y)
    (n : ℕ) : restrictionObj x n ⟶ restrictionObj y n :=
  @IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _
    (y.base.truncationOverHom n) (restrictionHom y n)
    (restrictionHom_isStronglyCartesian y n) _ _ _ _ (approximation_factor f n)
    (restrictionHom x n ≫ f.hom) (approximationApp_isHomLift f n)

/-- The restricted arrow lifts the truncation of its local base morphism. -/
theorem approximationApp_over {x y : CompleteLocalObject X}
    (f : CompleteLocalObject.Hom x y) (n : ℕ) :
    X.p.IsHomLift ((CompleteLocalObject.baseHom f).stageMap n) (approximationApp f n) :=
  @IsStronglyCartesian.map_isHomLift _ _ _ _ X.p _ _ _ _
    (y.base.truncationOverHom n) (restrictionHom y n)
    (restrictionHom_isStronglyCartesian y n) _ _ _ _ (approximation_factor f n)
    (restrictionHom x n ≫ f.hom) (approximationApp_isHomLift f n)

/-- Restricted arrows commute with successor comparisons. -/
theorem approximation_naturality {x y : CompleteLocalObject X}
    (f : CompleteLocalObject.Hom x y) (n : ℕ) :
    restrictionStep x n ≫ approximationApp f (n + 1) =
      approximationApp f n ≫ restrictionStep y n := sorry

/-- The natural stage family induced by a local morphism. -/
def approximationMap {x y : CompleteLocalObject X} (f : CompleteLocalObject.Hom x y) :
    Hom (restriction x) (restriction y) :=
  Hom.of (approximationApp f) (CompleteLocalObject.baseHom f)
    (approximationApp_over f) (approximation_naturality f)

/-- Restricting an identity arrow gives the identity natural stage family. -/
theorem approximation_map_id (x : CompleteLocalObject X) :
    approximationMap (𝟙 x) = 𝟙 (restriction x) := sorry

/-- Restriction preserves composition of local morphisms. -/
theorem approximation_map_comp {x y z : CompleteLocalObject X} (f : x ⟶ y) (g : y ⟶ z) :
    approximationMap (f ≫ g) = approximationMap f ≫ approximationMap g := sorry

end FormalObject

/-- The functor taking complete local objects and local morphisms to their
positive maximal-adic restriction systems. -/
def approximation (X : GroupoidsOver S) : CompleteLocalObject X ⥤ FormalObject X where
  obj := FormalObject.restriction
  map := FormalObject.approximationMap
  map_id := FormalObject.approximation_map_id
  map_comp := FormalObject.approximation_map_comp

/-- The object map of approximation is the chosen maximal-adic restriction system. -/
theorem approximation_obj {X : GroupoidsOver S} (x : CompleteLocalObject X) :
    (approximation X).obj x = FormalObject.restriction x := rfl

namespace FormalObject

variable {X : GroupoidsOver S}

/-- Stages of approximation are chosen cartesian restrictions to quotient spectra. -/
theorem approximation_family (x : CompleteLocalObject X) (n : ℕ) :
    ((GroupoidsOver.approximation X).obj x).objects n = restrictionObj x n := rfl

/-- Successor maps of approximation are the cartesian transitivity comparisons. -/
theorem approximation_step (x : CompleteLocalObject X) (n : ℕ) :
    ((GroupoidsOver.approximation X).obj x).step n = restrictionStep x n := rfl

/-- Components of the approximated arrow are the stagewise cartesian factorizations. -/
theorem approximation_map_app {x y : CompleteLocalObject X} (f : x ⟶ y) (n : ℕ) :
    ((GroupoidsOver.approximation X).map f).app n = approximationApp f n := rfl

end FormalObject

end AlgebraicGeometry.GroupoidsOver
