/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Quotient
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Cotangent

/-!
# Infinitesimal quotients of Artinian local algebras

Residue-identified Artinian local algebras have canonical quotients by the square
of the maximal ideal and by the relative infinitesimal denominator. Morphisms
induce residue-compatible local algebra maps on these quotients.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The quotient of an Artinian local algebra by the square of its maximal ideal. -/
noncomputable def modSquare (A : ArtinianLocalAlgCat Λ k) : ArtinianLocalAlgCat Λ k :=
  A.quotient (maximalIdeal A.carrier ^ 2) (Ideal.pow_le_self two_ne_zero)

/-- The carrier of the square quotient is the ring quotient by the maximal-ideal square. -/
theorem modSquare_carrier (A : ArtinianLocalAlgCat Λ k) :
    (modSquare A).carrier = (A.carrier ⧸ maximalIdeal A.carrier ^ 2) := sorry

/-- The square quotient is the categorical quotient by the maximal-ideal square. -/
theorem modSquare_spec (A : ArtinianLocalAlgCat Λ k) :
    modSquare A = A.quotient (maximalIdeal A.carrier ^ 2) (Ideal.pow_le_self two_ne_zero) :=
  sorry

/-- A local algebra morphism sends the source maximal-ideal square into the target square. -/
theorem modSquare_map_le {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    maximalIdeal B.carrier ^ 2 ≤ (maximalIdeal A.carrier ^ 2).comap f.hom := sorry

/-- The algebra map induced on maximal-ideal square quotients is local. -/
instance modSquareMap_isLocalHom {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsLocalHom (Ideal.quotientMapₐ (maximalIdeal A.carrier ^ 2) f.hom
      (modSquare_map_le f) : algebraHom (modSquare B) (modSquare A)) := sorry

/-- The induced square-quotient map respects the canonical residue identifications. -/
theorem modSquareMap_residue_compat {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    residueCompat (A := modSquare B) (B := modSquare A)
      (Ideal.quotientMapₐ (maximalIdeal A.carrier ^ 2) f.hom (modSquare_map_le f))
      (modSquareMap_isLocalHom f) = residueIsoHom (modSquare B) := sorry

/-- The canonical morphism of maximal-ideal square quotients induced by a local algebra map. -/
noncomputable def modSquareMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    modSquare B ⟶ modSquare A :=
  Hom.of (Ideal.quotientMapₐ (maximalIdeal A.carrier ^ 2) f.hom (modSquare_map_le f))
    (modSquareMap_isLocalHom f) (modSquareMap_residue_compat f)

/-- The underlying algebra map of the square-quotient morphism is the induced quotient map. -/
theorem modSquareMap_hom {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    (modSquareMap f).hom =
      Ideal.quotientMapₐ (maximalIdeal A.carrier ^ 2) f.hom (modSquare_map_le f) :=
  sorry

/-- The quotient by the extension of the base residue kernel and the maximal-ideal square. -/
noncomputable def modRelative (A : ArtinianLocalAlgCat Λ k) : ArtinianLocalAlgCat Λ k :=
  A.quotient (relativeDenom A) (relativeDenom_le_maximalIdeal A)

/-- The carrier of the relative infinitesimal quotient is the ring quotient by its denominator. -/
theorem modRelative_carrier (A : ArtinianLocalAlgCat Λ k) :
    (modRelative A).carrier = (A.carrier ⧸ relativeDenom A) := sorry

/-- The relative infinitesimal quotient is the categorical quotient by the relative denominator. -/
theorem modRelative_spec (A : ArtinianLocalAlgCat Λ k) :
    modRelative A = A.quotient (relativeDenom A) (relativeDenom_le_maximalIdeal A) :=
  sorry

/-- A local algebra morphism sends the source relative denominator into the target denominator. -/
theorem relativeDenom_map_le {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    relativeDenom B ≤ (relativeDenom A).comap f.hom := sorry

/-- The algebra map induced on relative infinitesimal quotients is local. -/
instance modRelativeMap_isLocalHom {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsLocalHom (Ideal.quotientMapₐ (relativeDenom A) f.hom
      (relativeDenom_map_le f) : algebraHom (modRelative B) (modRelative A)) := sorry

/-- The induced relative-quotient map respects the canonical residue identifications. -/
theorem modRelativeMap_residue_compat {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    residueCompat (A := modRelative B) (B := modRelative A)
      (Ideal.quotientMapₐ (relativeDenom A) f.hom (relativeDenom_map_le f))
      (modRelativeMap_isLocalHom f) = residueIsoHom (modRelative B) := sorry

/-- The canonical morphism of relative infinitesimal quotients induced by a local algebra map. -/
noncomputable def modRelativeMap {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    modRelative B ⟶ modRelative A :=
  Hom.of (Ideal.quotientMapₐ (relativeDenom A) f.hom (relativeDenom_map_le f))
    (modRelativeMap_isLocalHom f) (modRelativeMap_residue_compat f)

/-- The underlying algebra map of the relative-quotient morphism is the induced quotient map. -/
theorem modRelativeMap_hom {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    (modRelativeMap f).hom = Ideal.quotientMapₐ (relativeDenom A) f.hom (relativeDenom_map_le f) :=
  sorry

end ArtinianLocalAlgCat
