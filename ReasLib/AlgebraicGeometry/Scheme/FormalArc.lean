/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.LocalRing.Cotangent.Surjective

/-!
# Formal arcs

A formal arc through a closed point is a morphism from the spectrum of a
complete discrete valuation ring which induces an isomorphism on residue fields.
-/

@[expose] public section

noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Scheme

/-- A formal arc through `p` with source the spectrum of the complete discrete valuation ring `R`. -/
structure FormalArc (X : Scheme.{u}) (p : closedPoints X) (R : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsCompleteLocalRing R] where
  /-- The morphism from the spectrum of the parameter ring. -/
  hom : Spec (.of R) ⟶ X
  /-- The closed point of the parameter spectrum maps to the marked point. -/
  hom_closedPoint : hom (IsLocalRing.closedPoint R) = p.1
  /-- The arc induces an isomorphism of residue fields. -/
  residueFieldMap_bijective :
    Function.Bijective (hom.residueFieldMap (IsLocalRing.closedPoint R))

namespace FormalArc

/-- Construct a formal arc from a local homomorphism out of the marked stalk which induces a
bijection on residue fields. -/
noncomputable def ofLocalHom {X : Scheme.{u}} (p : closedPoints X) (R : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsCompleteLocalRing R]
    (f : X.presheaf.stalk p.1 →+* R)
    [h_local : IsLocalHom f]
    (h_residue : Function.Bijective
      (IsLocalRing.ResidueField.map f)) :
    FormalArc X p R where
  hom := (SpecToEquivOfLocalRing X (.of R)).symm
    ⟨p.1, ⟨CommRingCat.ofHom f, h_local⟩⟩
  hom_closedPoint := sorry
  residueFieldMap_bijective := sorry

/-- The morphism underlying an arc constructed from a local stalk homomorphism is the canonical
morphism supplied by `SpecToEquivOfLocalRing`. -/
theorem ofLocalHom_hom {X : Scheme.{u}} (p : closedPoints X) (R : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsCompleteLocalRing R]
    (f : X.presheaf.stalk p.1 →+* R)
    [h_local : IsLocalHom f]
    (h_residue : Function.Bijective
      (IsLocalRing.ResidueField.map f)) :
    (ofLocalHom p R f h_residue).hom =
      (SpecToEquivOfLocalRing X (.of R)).symm
        ⟨p.1, ⟨CommRingCat.ofHom f, h_local⟩⟩ := sorry

/-- The local ring homomorphism on stalks induced by a formal arc. -/
noncomputable def stalkMap {X : Scheme.{u}} {p : closedPoints X} {R : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsCompleteLocalRing R]
    (A : FormalArc X p R) : X.presheaf.stalk p.1 →+* R :=
  ((X.presheaf.stalkCongr (.of_eq A.hom_closedPoint.symm)).hom ≫
    (Scheme.stalkClosedPointTo A.hom :
      X.presheaf.stalk (A.hom (IsLocalRing.closedPoint R)) ⟶ CommRingCat.of R)).hom

/-- The stalk map induced by a formal arc is local. -/
theorem stalkMap_isLocal {X : Scheme.{u}} {p : closedPoints X} {R : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsCompleteLocalRing R]
    (A : FormalArc X p R) :
    IsLocalHom A.stalkMap := sorry

/-- The map on cotangent spaces induced by a formal arc. -/
noncomputable def cotangentMap {X : Scheme.{u}} {p : closedPoints X} {R : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsCompleteLocalRing R]
    (A : FormalArc X p R) :
    IsLocalRing.CotangentSpace (X.presheaf.stalk p.1) →
      IsLocalRing.CotangentSpace R :=
  @IsLocalRing.CotangentSpace.map
    (X.presheaf.stalk p.1) R
    inferInstance inferInstance inferInstance inferInstance
    (RingHom.toAlgebra A.stalkMap) A.stalkMap_isLocal

/-- A formal arc is nonsingular when its induced map on cotangent spaces is surjective. -/
def IsNonsingular {X : Scheme.{u}} {p : closedPoints X} {R : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsCompleteLocalRing R]
    (A : FormalArc X p R) : Prop :=
  Function.Surjective A.cotangentMap

/-- Nonsingularity of a formal arc is exactly surjectivity of its cotangent-space map. -/
theorem isNonsingular_iff {X : Scheme.{u}} {p : closedPoints X} {R : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsCompleteLocalRing R]
    (A : FormalArc X p R) :
    A.IsNonsingular ↔ Function.Surjective A.cotangentMap := sorry

/-- The defining closed-point and residue-field conditions of a formal arc. -/
theorem spec {X : Scheme.{u}} {p : closedPoints X} {R : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsCompleteLocalRing R]
    (A : FormalArc X p R) :
    (A.hom (IsLocalRing.closedPoint R) = p.1) ∧
      Function.Bijective (A.hom.residueFieldMap (IsLocalRing.closedPoint R)) := sorry

end FormalArc

end AlgebraicGeometry.Scheme
