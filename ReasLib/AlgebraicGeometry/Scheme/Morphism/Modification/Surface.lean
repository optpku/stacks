/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import ReasLib.RingTheory.Normal.Local

/-!
# Surface modifications

This module packages a two-dimensional local normal base together with a
modification and an explicit enumeration of the irreducible components of its
special fibre.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A surface modification over a two-dimensional local Noetherian normal ring. -/
structure SurfaceModification (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsNormalRing A] where
  /-- The base ring has Krull dimension two. -/
  dimensionProof : ringKrullDim A = 2
  /-- The scheme carrying the modification. -/
  X : Scheme.{u}
  /-- The morphism to the affine base scheme. -/
  f : X ⟶ Spec (CommRingCat.of A)
  /-- The morphism is a modification. -/
  modification : IsModification f
  /-- The finite index type for the special-fibre components. -/
  r : ℕ
  /-- An enumeration of the irreducible components of the special fibre. -/
  componentEquiv : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))

namespace SurfaceModification

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A]

/-- Construct a surface modification from a dimension-two base, a modification,
and an explicit finite enumeration of its special-fibre components. -/
def of (dimensionProof : ringKrullDim A = 2) (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of A)) (modification : IsModification f) (r : ℕ)
    (componentEquiv : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))) :
    SurfaceModification A where
  dimensionProof := dimensionProof
  X := X
  f := f
  modification := modification
  r := r
  componentEquiv := componentEquiv

/-- A surface modification has a dimension-two base and a modification morphism. -/
theorem spec (setup : SurfaceModification A) :
    ringKrullDim A = 2 ∧ IsModification setup.f := sorry

/-- The local-ring structure on the base ring of a surface modification. -/
@[stacks 0AX8]
def localRing (S : SurfaceModification A) : IsLocalRing A := inferInstance

/-- The Noetherian-ring structure on the base ring of a surface modification. -/
@[stacks 0AX8]
def noetherianRing (S : SurfaceModification A) : IsNoetherianRing A :=
  inferInstance

/-- The normal-ring structure on the base ring of a surface modification. -/
@[stacks 0AX8]
def normalRing (S : SurfaceModification A) : IsNormalRing A := inferInstance

/-- The domain structure on the base ring of a surface modification. -/
@[stacks 0AX8]
def domain (S : SurfaceModification A) : IsDomain A := inferInstance

/-- The Krull dimension of the base ring of a surface modification is two. -/
@[stacks 0AX8]
def dimension (S : SurfaceModification A) : ringKrullDim A = 2 := S.dimensionProof

/-- The maximal ideal of the base ring of a surface modification. -/
@[stacks 0AX8]
noncomputable def maximalIdeal (S : SurfaceModification A) : Ideal A :=
  IsLocalRing.maximalIdeal A

/-- The residue field of the base ring of a surface modification. -/
@[stacks 0AX8]
abbrev residueField (S : SurfaceModification A) : Type u :=
  IsLocalRing.ResidueField A

/-- The affine base scheme of a surface modification. -/
@[stacks 0AX8]
noncomputable abbrev base (S : SurfaceModification A) : Scheme.{u} :=
  Spec (CommRingCat.of A)

/-- The closed point of the affine base scheme of a surface modification. -/
@[stacks 0AX8]
noncomputable def closedPoint (S : SurfaceModification A) : PrimeSpectrum A :=
  IsLocalRing.closedPoint A

/-- The punctured spectrum of the affine base scheme of a surface modification. -/
@[stacks 0AX8]
noncomputable abbrev puncturedSpectrum (S : SurfaceModification A) : Scheme.{u} :=
  PuncturedSpectrum.scheme A

/-- The modification property of the morphism in a surface modification. -/
@[stacks 0AX8]
def isModification (S : SurfaceModification A) : IsModification S.f :=
  S.modification

/-- The special-fibre component enumeration of a surface modification. -/
@[stacks 0AX8]
def components (S : SurfaceModification A) :
    Fin S.r ≃ irreducibleComponents (S.f.fiber (IsLocalRing.closedPoint A)) :=
  S.componentEquiv

end SurfaceModification

end AlgebraicGeometry
