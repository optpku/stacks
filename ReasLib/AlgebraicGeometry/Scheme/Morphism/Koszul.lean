/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection

/-!
# Koszul morphisms at a point

This module defines the pointwise geometric factorization condition for a scheme morphism to be
Koszul and relates its pointwise form to the established local-complete-intersection property.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A scheme morphism is Koszul at `x` when it is of finite type at `x` and, on an open
neighborhood of `x`, factors as a Koszul-regular immersion followed by a smooth morphism. -/
def KoszulAt (x : X) : Prop :=
  f.FiniteTypeAt x ∧
    ∃ U : X.Opens, x ∈ U ∧
      ∃ (P : Scheme.{u}) (i : U.toScheme ⟶ P) (π : P ⟶ S),
        IsKoszulRegularImmersion i ∧ Smooth π ∧ i ≫ π = U.ι ≫ f

/-- The complete finite-type and local-factorization characterization of `f.KoszulAt x`. -/
theorem koszulAt_iff (x : X) :
    f.KoszulAt x ↔
      f.FiniteTypeAt x ∧
        ∃ U : X.Opens, x ∈ U ∧
          ∃ (P : Scheme.{u}) (i : U.toScheme ⟶ P) (π : P ⟶ S),
            IsKoszulRegularImmersion i ∧ Smooth π ∧ i ≫ π = U.ι ≫ f := sorry

namespace KoszulAt

/-- A morphism that is Koszul at a point is of finite type there. -/
theorem finiteTypeAt {x : X} (h : f.KoszulAt x) :
    f.FiniteTypeAt x := sorry

/-- A Koszul-at-point hypothesis supplies its open neighborhood and geometric factorization. -/
theorem exists_factorization {x : X} (h : f.KoszulAt x) :
    ∃ U : X.Opens, x ∈ U ∧
      ∃ (P : Scheme.{u}) (i : U.toScheme ⟶ P) (π : P ⟶ S),
        IsKoszulRegularImmersion i ∧ Smooth π ∧ i ≫ π = U.ι ≫ f := sorry

end KoszulAt
end Scheme.Hom

namespace LocallyOfType

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A scheme morphism is locally of complete-intersection type exactly when it is Koszul at
every point of its source. -/
theorem isLocalCompleteIntersection_iff_forall_koszulAt :
    LocallyOfType RingHom.IsLocalCompleteIntersection f ↔
      ∀ x : X, f.KoszulAt x := sorry

/-- A locally complete-intersection scheme morphism is Koszul at every chosen source point. -/
theorem koszulAt (hf : LocallyOfType RingHom.IsLocalCompleteIntersection f) (x : X) :
    f.KoszulAt x := sorry

end LocallyOfType
end AlgebraicGeometry
