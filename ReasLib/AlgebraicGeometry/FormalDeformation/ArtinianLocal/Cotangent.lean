/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import ReasLib.RingTheory.LocalRing.Cotangent.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Instances

/-!
# Cotangent surjectivity for residue-identified Artinian local algebras

Morphisms induce maps on ordinary cotangent spaces and on relative quotients by
the extension of `RingHom.ker (algebraMap Λ k)` and the square of the maximal ideal.
Surjectivity of either induced map is equivalent to surjectivity of the morphism.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The ideal `m_Λ A + m_A²`, where `m_Λ` is `RingHom.ker (algebraMap Λ k)`. -/
def relativeDenom (A : ArtinianLocalAlgCat Λ k) : Ideal A.carrier :=
  (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A.carrier) ⊔ maximalIdeal A.carrier ^ 2

/-- `relativeDenom A` is the sum of the extension of `ker (algebraMap Λ k)` and the square of
the maximal ideal. -/
theorem relativeDenom_spec (A : ArtinianLocalAlgCat Λ k) :
    relativeDenom A =
      (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A.carrier) ⊔
        maximalIdeal A.carrier ^ 2 :=
  rfl

/-- The relative denominator `m_Λ A + m_A²` is contained in the maximal ideal. -/
theorem relativeDenom_le_maximalIdeal (A : ArtinianLocalAlgCat Λ k) :
    relativeDenom A ≤ maximalIdeal A.carrier := sorry

/-- The `Λ`-submodule of `maximalIdeal A.carrier` cut out by `relativeDenom A`. -/
def relativeSubmodule (A : ArtinianLocalAlgCat Λ k) :
    Submodule Λ (maximalIdeal A.carrier) :=
  (Submodule.comap (maximalIdeal A.carrier).subtype (relativeDenom A)).restrictScalars Λ

/-- Membership in `relativeSubmodule A` is membership of the underlying element in
`relativeDenom A`. -/
theorem mem_relativeSubmodule {A : ArtinianLocalAlgCat Λ k} {x : maximalIdeal A.carrier} :
    x ∈ relativeSubmodule A ↔ (x : A.carrier) ∈ relativeDenom A :=
  Iff.rfl

namespace Hom

/-- The restriction of a morphism in `ArtinianLocalAlgCat` to maximal ideals. -/
def mapMaximalIdeal {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B) :
    maximalIdeal A.carrier →ₗ[Λ] maximalIdeal B.carrier where
  toFun x :=
    ⟨f.hom (x : A.carrier),
      (maximalIdeal_comap (f.hom : A.carrier →+* B.carrier)).symm.le x.2⟩
  map_add' x y := Subtype.ext (map_add f.hom (x : A.carrier) (y : A.carrier))
  map_smul' r x :=
    Subtype.ext (LinearMap.map_smul f.hom.toLinearMap r (x : A.carrier))

/-- The maximal-ideal restriction of a morphism applies as the underlying algebra map. -/
theorem mapMaximalIdeal_apply {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B)
    (x : maximalIdeal A.carrier) :
    mapMaximalIdeal f x =
      ⟨f.hom (x : A.carrier),
        (maximalIdeal_comap (f.hom : A.carrier →+* B.carrier)).symm.le x.2⟩ :=
  rfl

/-- A morphism in `ArtinianLocalAlgCat` sends `relativeSubmodule` into the target
`relativeSubmodule`. -/
theorem relativeSubmodule_map_le {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B) :
    relativeSubmodule A ≤ (relativeSubmodule B).comap (mapMaximalIdeal f) := sorry

/-- The `Λ`-linear map of relative quotients `maximalIdeal ⧸ relativeSubmodule` induced by a
morphism in `ArtinianLocalAlgCat`. -/
def mapRelative {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B) :
    (maximalIdeal A.carrier ⧸ relativeSubmodule A) →ₗ[Λ]
      (maximalIdeal B.carrier ⧸ relativeSubmodule B) :=
  Submodule.mapQ (relativeSubmodule A) (relativeSubmodule B) (mapMaximalIdeal f)
    (relativeSubmodule_map_le f)

/-- The relative quotient map sends the class of an element of the maximal ideal to the class
of its image. -/
theorem mapRelative_mk {A B : ArtinianLocalAlgCat Λ k} (f : Hom A B)
    (x : maximalIdeal A.carrier) :
    mapRelative f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        ⟨f.hom (x : A.carrier),
          (maximalIdeal_comap (f.hom : A.carrier →+* B.carrier)).symm.le x.2⟩ :=
  rfl

/-- A residue-compatible Artinian local algebra morphism is surjective if and only if its
induced map on cotangent spaces is surjective. -/
theorem surjective_iff_mapAlgHom {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    Function.Surjective f.hom ↔ Function.Surjective (CotangentSpace.mapAlgHom f.hom) := sorry

/-- The induced ordinary cotangent map of a residue-compatible Artinian local algebra morphism
is surjective if and only if its induced relative cotangent map is surjective. -/
theorem mapAlgHom_surjective_iff_mapRelative {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    Function.Surjective (CotangentSpace.mapAlgHom f.hom) ↔
      Function.Surjective (mapRelative f) := sorry

/-- A residue-compatible Artinian local algebra morphism is surjective if and only if its
induced map on relative cotangent quotients is surjective. -/
theorem surjective_iff_mapRelative {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    Function.Surjective f.hom ↔ Function.Surjective (mapRelative f) := sorry

end Hom

end ArtinianLocalAlgCat
