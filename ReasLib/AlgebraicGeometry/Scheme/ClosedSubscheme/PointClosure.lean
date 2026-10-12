/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Reduced closures of points

This file provides the canonical reduced induced scheme structure on the
closure of a point and its functorial maps along scheme morphisms.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PointClosure

variable {X Y Z : Scheme.{u}}

/-- The closed subset given by the closure of a singleton point. -/
def closedSubset {X : Scheme.{u}} (x : X) : Closeds X :=
  .closure ({x} : Set X)

/-- The carrier of the closed subset associated to a point is its singleton closure. -/
theorem coe_closedSubset {X : Scheme.{u}} (x : X) :
    (closedSubset x : Set X) = closure ({x} : Set X) := sorry

/-- The canonical reduced induced scheme structure on the closure of a point. -/
noncomputable def reducedStructure {X : Scheme.{u}} (x : X) :
    ClosedSubschemeStructure (closedSubset x) :=
  ClosedSubschemeStructure.reduced (closedSubset x)

/-- The scheme with the reduced induced structure on the closure of a point. -/
noncomputable def scheme {X : Scheme.{u}} (x : X) : Scheme.{u} :=
  (reducedStructure x).subscheme

/-- The canonical closed immersion from the reduced point closure into the ambient scheme. -/
noncomputable def ι {X : Scheme.{u}} (x : X) : scheme x ⟶ X :=
  (reducedStructure x).ι

/-- The range of the canonical immersion is the singleton closure. -/
theorem range_ι {X : Scheme.{u}} (x : X) :
    Set.range (ι x) = closure ({x} : Set X) := sorry

/-- The canonical reduced point-closure scheme is reduced. -/
instance scheme_isReduced {X : Scheme.{u}} (x : X) : IsReduced (scheme x) := sorry

/-- The canonical morphism between reduced point closures induced by a scheme morphism. -/
noncomputable def map (f : X ⟶ Y) (x : X) : scheme x ⟶ scheme (f x) :=
  IdealSheafData.subschemeMap
    (IdealSheafData.vanishingIdeal (closedSubset x))
    (IdealSheafData.vanishingIdeal (closedSubset (f x))) f <| by
      rw [IdealSheafData.map_vanishingIdeal]
      apply IdealSheafData.vanishingIdeal_antimono
      apply Closeds.closure_le.mpr
      simpa [closedSubset] using
        (image_closure_subset_closure_image (s := ({x} : Set X)) f.continuous)

/-- The map on reduced point closures commutes with the canonical immersions. -/
theorem map_ι (f : X ⟶ Y) (x : X) :
    map f x ≫ ι (f x) = ι x ≫ f := sorry

/-- The map on reduced point closures associated to an identity morphism is the identity. -/
theorem map_id (x : X) :
    map (𝟙 X) x = 𝟙 (scheme x) := sorry

/-- Maps on reduced point closures preserve composition. -/
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    map (f ≫ g) x = map f x ≫ map g (f x) := sorry

/-- The map on reduced point closures with its target indexed by a specified image point. -/
noncomputable def mapOfEq (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    scheme x ⟶ scheme y :=
  map f x ≫ eqToHom (congrArg (fun z : Y ↦ scheme z) h)

/-- An equality-indexed map on reduced point closures commutes with the canonical immersions. -/
theorem mapOfEq_ι (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    mapOfEq f x y h ≫ ι y = ι x ≫ f := sorry

/-- The equality-indexed map associated to an identity morphism is the identity. -/
theorem mapOfEq_id (x : X) :
    mapOfEq (𝟙 X) x x rfl = 𝟙 (scheme x) := sorry

/-- Equality-indexed maps on reduced point closures preserve composition. -/
theorem mapOfEq_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (hxy : f x = y) (hyz : g y = z) :
    mapOfEq (f ≫ g) x z ((congrArg (fun w : Y ↦ g w) hxy).trans hyz) =
      mapOfEq f x y hxy ≫ mapOfEq g y z hyz := sorry

end AlgebraicGeometry.Scheme.PointClosure
