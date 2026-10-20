/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.QuadricCone

/-!
# The punctured affine quadratic cone

This module records the vertex `(x, y, z)`, the punctured open `U = C \ {(x, y, z)}`,
the standard affine charts `D(x)` and `D(y)`, and the ruling invertible sheaf on `U`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open CategoryTheory.MonoidalCategory
open Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.QuadricCone

/-- The vertex ideal `(x, y, z)` of the affine quadratic cone. -/
def vertexIdeal (k : Type u) [CommRing k] : Ideal (coordinateRing k) :=
  Ideal.span {coord k 0, coord k 1, coord k 2}

/-- The vertex ideal is the span of the three coordinate classes. -/
theorem vertexIdeal_eq_span (k : Type u) [CommRing k] :
    vertexIdeal k = Ideal.span {coord k 0, coord k 1, coord k 2} :=
  sorry

/-- The vertex ideal `(x, y, z)` is maximal when `k` is a field. -/
instance vertexIdeal_isMaximal (k : Type u) [Field k] : (vertexIdeal k).IsMaximal :=
  sorry

/-- The closed point `(x, y, z)` of the affine quadratic cone. -/
def vertex (k : Type u) [Field k] : scheme k :=
  ⟨vertexIdeal k, (vertexIdeal_isMaximal k).isPrime⟩

/-- The prime ideal of the vertex is the span of the three coordinate classes. -/
theorem vertex_asIdeal (k : Type u) [Field k] :
    (vertex k).asIdeal = vertexIdeal k :=
  sorry

/-- The singleton consisting of the vertex is closed. -/
theorem isClosed_singleton_vertex (k : Type u) [Field k] :
    IsClosed ({vertex k} : Set (scheme k)) :=
  sorry

/-- The punctured cone `U = C \ {(x, y, z)}`. -/
def puncturedOpen (k : Type u) [Field k] : (scheme k).Opens :=
  ⟨({vertex k} : Set (scheme k))ᶜ, (isClosed_singleton_vertex k).isOpen_compl⟩

/-- A point of the cone lies in the punctured open if and only if it is not the vertex. -/
theorem mem_puncturedOpen_iff_ne_vertex (k : Type u) [Field k] {x : scheme k} :
    x ∈ puncturedOpen k ↔ x ≠ vertex k :=
  sorry

/-- The basic open `D(x)` on the affine quadratic cone. -/
def chartX (k : Type u) [CommRing k] : (scheme k).Opens :=
  (scheme k).basicOpen ((ΓSpecIso (CommRingCat.of (coordinateRing k))).inv (coord k 0))

/-- The basic open `D(y)` on the affine quadratic cone. -/
def chartY (k : Type u) [CommRing k] : (scheme k).Opens :=
  (scheme k).basicOpen ((ΓSpecIso (CommRingCat.of (coordinateRing k))).inv (coord k 1))

/-- The punctured cone is the union of the basic opens `D(x)` and `D(y)`. -/
theorem puncturedOpen_eq_chartX_sup_chartY (k : Type u) [Field k] :
    puncturedOpen k = chartX k ⊔ chartY k :=
  sorry

/-- The basic open `D(x)` is affine. -/
theorem chartX_isAffineOpen (k : Type u) [CommRing k] : IsAffineOpen (chartX k) :=
  sorry

/-- The basic open `D(y)` is affine. -/
theorem chartY_isAffineOpen (k : Type u) [CommRing k] : IsAffineOpen (chartY k) :=
  sorry

/-- The restriction of the ruling `V(x, z)` to the punctured cone. -/
def rulingOnPunctured (k : Type u) [Field k] : (puncturedOpen k).toScheme.IdealSheafData :=
  (rulingIdealSheaf k).comap (puncturedOpen k).ι

/-- The restricted ruling is an effective Cartier divisor on the punctured cone. -/
instance rulingOnPunctured_isEffectiveCartierDivisor (k : Type u) [Field k] :
    IsEffectiveCartierDivisor (rulingOnPunctured k).subschemeι :=
  sorry

/-- The invertible sheaf on the punctured cone associated to the restricted ruling. -/
def rulingSheaf (k : Type u) [Field k] : (puncturedOpen k).toScheme.Modules :=
  (rulingOnPunctured k).associatedSheaf

/-- The ruling sheaf on the punctured cone is locally free of rank one. -/
instance rulingSheaf_isFiniteLocallyFreeOfRankOne (k : Type u) [Field k] :
    Modules.IsFiniteLocallyFreeOfRank 1 (rulingSheaf k) :=
  sorry

/-- The ruling sheaf on the punctured cone is not isomorphic to the structure sheaf. -/
theorem rulingSheaf_not_isUnitObject (k : Type u) [Field k] :
    ¬ Nonempty (rulingSheaf k ≅ 𝟙_ (puncturedOpen k).toScheme.Modules) :=
  sorry

/-- The punctured affine quadratic cone over a field admits a nontrivial invertible sheaf. -/
theorem exists_nontrivial_invertibleSheaf (k : Type u) [Field k] :
    ∃ L : (puncturedOpen k).toScheme.Modules,
      IsFiniteLocallyFreeOfRank 1 L ∧
        ¬ Nonempty (L ≅ 𝟙_ (puncturedOpen k).toScheme.Modules) :=
  sorry

end AlgebraicGeometry.QuadricCone
