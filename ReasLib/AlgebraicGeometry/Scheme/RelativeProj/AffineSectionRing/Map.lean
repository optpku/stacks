/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.AffineSectionRing
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GradedMap

/-!
# Componentwise maps of graded section rings

Degreewise additive maps induce additive maps of section rings. Unit and
multiplication laws package the same map as a graded ring homomorphism.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry
open SheafOfModules.RingedSite
open scoped DirectSum
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.RelativeProjAffineSectionRing.SectionMap

variable {T U : Scheme.{u}}
variable (A : GradedAlgebraSheaf.{u, u} T.sheaf)
variable (B : GradedAlgebraSheaf.{u, u} U.sheaf)
variable [hA : A.IsCommutative] [hB : B.IsCommutative]
variable (f : ∀ n, RingedSpace.GradedAlgebraSections.degree A n →+
  RingedSpace.GradedAlgebraSections.degree B n)

/-- The additive map of section rings induced componentwise by degree maps. -/
def addMap : ring A →+ ring B := DirectSum.map f

/-- A componentwise map sends a homogeneous generator to its component image. -/
theorem addMap_of (n : ℕ) (x : RingedSpace.GradedAlgebraSections.degree A n) :
    addMap A B f (DirectSum.of (RingedSpace.GradedAlgebraSections.degree A) n x) =
      DirectSum.of (RingedSpace.GradedAlgebraSections.degree B) n (f n x) := by
  exact DirectSum.map_of f n x

variable (h1 : addMap A B f 1 = 1)
variable (hm : ∀ x y, addMap A B f (x * y) = addMap A B f x * addMap A B f y)

/-- A componentwise additive map preserving unit and products is a ring map. -/
def ringMap : ring A →+* ring B where
  toAddMonoidHom := addMap A B f
  map_one' := h1
  map_mul' := hm

/-- Ring packaging preserves the specified underlying additive map. -/
theorem ringMap_toAddMonoidHom :
    (ringMap A B f h1 hm).toAddMonoidHom = addMap A B f := rfl

/-- The ring map acts on homogeneous generators by the specified degree maps. -/
theorem ringMap_of (n : ℕ) (x : RingedSpace.GradedAlgebraSections.degree A n) :
    ringMap A B f h1 hm (DirectSum.of (RingedSpace.GradedAlgebraSections.degree A) n x) =
      DirectSum.of (RingedSpace.GradedAlgebraSections.degree B) n (f n x) :=
  addMap_of A B f n x

/-- The componentwise ring map preserves every homogeneous summand. -/
theorem ringMap_mem (n : ℕ) (x : ring A) (hx : x ∈ grading A n) :
    ringMap A B f h1 hm x ∈ grading B n := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨f n a, (ringMap_of A B f h1 hm n a).symm⟩

/-- The componentwise ring map with its homogeneous-summand preservation. -/
def gradedMap : grading A →+*ᵍ grading B where
  toRingHom := ringMap A B f h1 hm
  map_mem := fun {n x} hx ↦ ringMap_mem A B f h1 hm n x hx

/-- Graded packaging preserves the underlying componentwise ring map. -/
theorem gradedMap_toRingHom :
    (gradedMap A B f h1 hm).toRingHom = ringMap A B f h1 hm := rfl

/-- A specified full-domain graded section-ring map induces its projective map. -/
def projMap (ψ : grading A →+*ᵍ grading B) (hTop : projMapDomain ψ = ⊤) :
    scheme B ⟶ scheme A :=
  Proj.AssociatedModule.GradedMap.fullMap ψ hTop

/-- Homogeneous fractions induce the comparison of twists for a full-domain map. -/
def twistHom (ψ : grading A →+*ᵍ grading B) (hTop : projMapDomain ψ = ⊤) (n : ℤ) :
    (Scheme.Modules.pullback (projMap A B ψ hTop)).obj
      (Proj.AssociatedModule.twistingSheaf (grading A) n) ⟶
    Proj.AssociatedModule.twistingSheaf (grading B) n :=
  Proj.AssociatedModule.GradedMap.hom ψ hTop n

end AlgebraicGeometry.Scheme.RelativeProjAffineSectionRing.SectionMap

