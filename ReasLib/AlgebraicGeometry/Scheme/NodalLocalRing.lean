/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.RingHom.Fiber.Quotient
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.LocalRing.Nodal

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

namespace NodalLocalRing

/-- For a Nagata nodal local ring, the canonical quadratic algebra is the closed fiber of the
normalization. -/
theorem normalizationFiber_equiv
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    Nonempty
      (NodalLocalRing.quadraticAlgebra A ≃ₐ[ResidueField A]
        (maximalIdeal A).Fiber (Normalization.normalizationRing A)) := sorry

/-- For a complete nodal local ring, the projectivized tangent cone is the spectrum of the
canonical quadratic algebra. -/
theorem associatedGradedProj_iso
    (k : Type u) [Field k]
    (A : Type u) [CommRing A] [IsCompleteLocalRing A] [Algebra k A]
    [IsNodalLocalRing A] [Algebra.IsSeparableOver k (ResidueField A)] :
    Nonempty
      (Proj (Ideal.AssociatedGraded.grade (maximalIdeal A)) ≅
        Spec (CommRingCat.of (NodalLocalRing.quadraticAlgebra A))) := sorry

/-- For a locally Noetherian scheme over a field, the normalization fiber at a nodal point is the
spectrum of the canonical quadratic algebra of the stalk. -/
theorem normalizationFiber_iso_specQuadraticAlgebra
    {k : Type u} [Field k] (X : SchemeOverField k) [IsLocallyNoetherian X.left]
    (x : X.left) [IsNodalLocalRing (stalkRing X x)]
    [Algebra.IsSeparableOver k (ResidueField (stalkRing X x))] :
    Nonempty
      (Spec (CommRingCat.of (NodalLocalRing.quadraticAlgebra (stalkRing X x))) ≅
        Scheme.Hom.fiber (Scheme.normalizationTo X.left) x) := sorry

end NodalLocalRing
