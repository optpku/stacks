/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Module
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

/-!
# Global sections of proper schemes over fields

This module records finiteness, factorization, and geometric properties of the
global-sections algebra of a proper scheme over a field.
-/

@[expose] public section

open CommRingCat TopologicalSpace

universe u

namespace AlgebraicGeometry

open Scheme.Hom

section

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The global-sections algebra of a proper scheme over a field is finite-dimensional. -/
instance globalSectionsFiniteDimensional [IsProper f] :
    FiniteDimensional k (globalSectionsAlg f) := sorry

/-- The ring of global sections of a proper scheme over a field is Artinian. -/
instance globalSectionsIsArtinianRing [IsProper f] :
    IsArtinianRing (globalSectionsAlg f) := sorry

/-- The global-sections algebra of a proper scheme over a field is a finite product of local
Artinian algebras indexed by the connected components of the scheme. -/
theorem globalSectionsLocalArtinianFactorization [IsProper f] :
    ∃ (_ : Fintype (ConnectedComponents X.carrier))
      (A : ConnectedComponents X.carrier → Type u)
      (_ : ∀ i, CommRing (A i))
      (_ : ∀ i, Algebra k (A i))
      (_ : ∀ i, IsLocalRing (A i))
      (_ : globalSectionsAlg f ≃ₐ[k] ∀ i, A i),
      ∀ i, IsArtinianRing (A i) := sorry

/-- If a proper scheme over a field is reduced, then its global-sections algebra is a finite
product of finite field extensions indexed by the connected components of the scheme. -/
theorem globalSectionsFieldFactorizationOfIsReduced [IsProper f] [IsReduced X] :
    ∃ (_ : Fintype (ConnectedComponents X.carrier))
      (K : ConnectedComponents X.carrier → Type u)
      (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i))
      (_ : globalSectionsAlg f ≃ₐ[k] ∀ i, K i),
      ∀ i, FiniteDimensional k (K i) := sorry

/-- The global-sections ring of a reduced, connected proper scheme over a field is a field. -/
theorem globalSectionsIsField [IsProper f] [IsReduced X] [ConnectedSpace X] :
    IsField (Scheme.globalSectionsRing X) := sorry

/-- The affine global-sections morphism of a geometrically reduced proper scheme over a field is
geometrically reduced. -/
instance globalSectionsGeometricallyReduced [IsProper f] [GeometricallyReduced f] :
    GeometricallyReduced (globalSectionsSpecMap f) := sorry

/-- If a proper scheme over a field is geometrically reduced, then its global-sections algebra is
a finite product of finite separable field extensions indexed by the connected components. -/
theorem globalSectionsSeparableFieldFactorizationOfGeometricallyReduced
    [IsProper f] [GeometricallyReduced f] :
    ∃ (_ : Fintype (ConnectedComponents X.carrier))
      (K : ConnectedComponents X.carrier → Type u)
      (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra k (K i))
      (_ : globalSectionsAlg f ≃ₐ[k] ∀ i, K i),
      ∀ i, FiniteDimensional k (K i) ∧ Algebra.IsSeparable k (K i) := sorry

/-- The global-sections algebra of a connected geometrically reduced proper scheme over a field
is separable. -/
instance globalSectionsIsSeparable
    [IsProper f] [ConnectedSpace X] [GeometricallyReduced f] :
    Algebra.IsSeparable k (globalSectionsAlg f) := sorry

/-- The affine global-sections morphism of a geometrically connected proper scheme over a field
is geometrically irreducible. -/
instance globalSectionsGeometricallyIrreducibleOfGeometricallyConnected
    [IsProper f] [GeometricallyConnected f] :
    GeometricallyIrreducible (globalSectionsSpecMap f) := sorry

/-- The affine global-sections morphism of a geometrically irreducible proper scheme over a field
is geometrically irreducible. -/
instance globalSectionsGeometricallyIrreducibleOfGeometricallyIrreducible
    [IsProper f] [GeometricallyIrreducible f] :
    GeometricallyIrreducible (globalSectionsSpecMap f) := sorry

/-- The global-sections algebra of a reduced geometrically irreducible proper scheme over a field
is purely inseparable. -/
instance globalSectionsIsPurelyInseparable
    [IsProper f] [IsReduced X] [GeometricallyIrreducible f] :
    IsPurelyInseparable k (globalSectionsAlg f) := sorry

/-- For a geometrically reduced and geometrically connected proper scheme over a field, the
canonical map from the field to the ring of global sections is bijective. -/
theorem Scheme.GlobalSections.map_bijective_of_geometricallyReduced_geometricallyConnected
    [IsProper f] [GeometricallyReduced f] [GeometricallyConnected f] :
    Function.Bijective (globalSectionsMap f) := sorry

/-- For a geometrically integral proper scheme over a field, the canonical map from the field to
the ring of global sections is bijective. -/
theorem globalSectionsAlgebraMapBijectiveOfGeometricallyIntegral
    [IsProper f] [GeometricallyIntegral f] :
    Function.Bijective (globalSectionsMap f) := sorry

/-- For a proper scheme over a field, the canonical morphism to the spectrum of its global
sections is geometrically connected. -/
theorem geometricallyConnected_toSpecΓ_of_isProper [IsProper f] :
    geometrically (ConnectedSpace ·) X.toSpecΓ := sorry

namespace Scheme.GlobalSections

/-- For a geometrically reduced proper scheme over a field, the canonical map from the field to
the ring of global sections is bijective exactly when the scheme is geometrically connected. -/
theorem map_bijective_iff_geometricallyConnected_of_geometricallyReduced
    [IsProper f] [GeometricallyReduced f] :
    Function.Bijective (globalSectionsMap f) ↔ GeometricallyConnected f := sorry

end Scheme.GlobalSections

end

end AlgebraicGeometry
