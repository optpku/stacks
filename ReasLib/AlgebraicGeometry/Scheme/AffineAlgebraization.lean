/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A commutative Noetherian ring equipped with two nested ideals. -/
structure AffineAlgebraizationSetup (A : Type u) [CommRing A] [IsNoetherianRing A] where
  /-- The ideal defining the smaller closed subscheme. -/
  I : Ideal A
  /-- The ideal defining the larger closed subscheme. -/
  a : Ideal A
  /-- The smaller ideal is contained in the larger ideal. -/
  ideal_le : I ≤ a

namespace AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Construct a nested-ideal affine algebraization setup. -/
def ofIdeals (I a : Ideal A) (ideal_le : I ≤ a) : AffineAlgebraizationSetup A :=
  ⟨I, a, ideal_le⟩

/-- The affine scheme associated to the ambient ring. -/
abbrev X (_ : AffineAlgebraizationSetup A) : Scheme :=
  Spec (CommRingCat.of A)

/-- The affine scheme associated to the quotient by the smaller ideal. -/
abbrev Y (S : AffineAlgebraizationSetup A) : Scheme :=
  Spec (CommRingCat.of (A ⧸ S.I))

/-- The canonical morphism from the quotient by the smaller ideal to the ambient spectrum. -/
def y (S : AffineAlgebraizationSetup A) : S.Y ⟶ S.X :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk S.I))

/-- The affine scheme associated to the quotient by the larger ideal. -/
abbrev Z (S : AffineAlgebraizationSetup A) : Scheme :=
  Spec (CommRingCat.of (A ⧸ S.a))

/-- The canonical morphism from the quotient by the larger ideal to the ambient spectrum. -/
def z (S : AffineAlgebraizationSetup A) : S.Z ⟶ S.X :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk S.a))

/-- The open complement of the closed support defined by the larger ideal. -/
def U (S : AffineAlgebraizationSetup A) : S.X.Opens :=
  (Scheme.idealSheafDataOfIdealOnSpec S.a).openComplement

end AffineAlgebraizationSetup

end AlgebraicGeometry
