/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.RingTheory.RestrictedPowerSeries.NaiveCotangent
public import ReasLib.RingTheory.Topology.AdicStar
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.Topology.FiniteType

/-! # Presentation independence of restricted naive cotangent complexes -/

@[expose] public section

open CategoryTheory
open HomotopyCategory
open TopologicalRing

universe u

namespace Algebra.NaiveCotangent.Restricted

variable {A B : Type u} [CommRing A] [TopologicalSpace A]
variable [CommRing B] [TopologicalSpace B] [Algebra A B]
variable {ι ι' : Type u} [Fintype ι] [Fintype ι']

/-- The morphism in `K(B)` induced by a morphism of restricted presentations,
via the usual formulas on `J / J²` and on `dx_i`. -/
noncomputable def mapNaiveCotangent [IsTopologicalRing A] [IsLinearTopology A A]
    {P : Presentation A B ι} {Q : Presentation A B ι'} (f : Presentation.Hom P Q) :
    (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent P) ⟶
      (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent Q) :=
  (quotient (ModuleCat B) (ComplexShape.down ℕ)).map (chainMap f)

variable [IsAdicStarRing A] [IsAdicStarRing B]

/-- Continuous maps between topological quotient presentations of an adic
topologically finite-type arrow of adic-star rings induce the same map in the
homotopy category. -/
theorem mapNaiveCotangent_eq
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (P : Presentation A B ι) (Q : Presentation A B ι')
    (hP : P.IsTopological) (hQ : Q.IsTopological)
    (f g : Presentation.Hom P Q) :
    mapNaiveCotangent f = mapNaiveCotangent g := sorry

/-- Two finite topological quotient presentations of an adic topologically
finite-type arrow of adic-star rings admit a continuous presentation morphism. -/
theorem hom_nonempty
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (P : Presentation A B ι) (Q : Presentation A B ι')
    (hP : P.IsTopological) (hQ : Q.IsTopological) :
    Nonempty (Presentation.Hom P Q) := sorry

/-- The restricted Jacobian complexes of two finite topological quotient
presentations of an adic topologically finite-type arrow of adic-star rings
are homotopy equivalent. -/
theorem homotopyEquiv_nonempty
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (P : Presentation A B ι) (Q : Presentation A B ι')
    (hP : P.IsTopological) (hQ : Q.IsTopological) :
    Nonempty (HomotopyEquiv (naiveCotangent P) (naiveCotangent Q)) := sorry

/-- Two finite topological quotient presentations of an adic topologically
finite-type arrow of adic-star rings determine a unique isomorphism in the
homotopy category whose map is induced by every continuous presentation morphism. -/
theorem isoUnique
    (hφ : Continuous (algebraMap A B))
    (h_adic : (algebraMap A B).IsAdicHom)
    (h_tft : (algebraMap A B).TopologicallyOfFiniteType)
    (P : Presentation A B ι) (Q : Presentation A B ι')
    (hP : P.IsTopological) (hQ : Q.IsTopological) :
    ∃! e :
      (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent P) ≅
        (quotient (ModuleCat B) (ComplexShape.down ℕ)).obj (naiveCotangent Q),
      ∀ f : Presentation.Hom P Q, e.hom = mapNaiveCotangent f := sorry

end Algebra.NaiveCotangent.Restricted
