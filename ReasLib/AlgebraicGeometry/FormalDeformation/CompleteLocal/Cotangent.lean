/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import ReasLib.RingTheory.LocalRing.Cotangent.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Instances

/-!
# Cotangent surjectivity for residue-identified complete local algebras

Morphisms induce maps on ordinary cotangent spaces and on relative quotients by
the extension of `RingHom.ker (algebraMap Λ k)` and the square of the maximal ideal.
Surjectivity of either induced map is equivalent to surjectivity of the morphism.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace CompleteLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The ideal `m_Λ R + m_R²`, where `m_Λ` is `RingHom.ker (algebraMap Λ k)`. -/
def relativeDenom (R : CompleteLocalAlgCat Λ k) : Ideal R.carrier :=
  (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ R.carrier) ⊔ R.maximalIdeal ^ 2

/-- `relativeDenom R` is the sum of the extension of `ker (algebraMap Λ k)` and the square of
the maximal ideal. -/
theorem relativeDenom_spec (R : CompleteLocalAlgCat Λ k) :
    relativeDenom R =
      (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ R.carrier) ⊔
        R.maximalIdeal ^ 2 :=
  rfl

/-- The relative denominator `m_Λ R + m_R²` is contained in the maximal ideal. -/
theorem relativeDenom_le_maximalIdeal (R : CompleteLocalAlgCat Λ k) :
    relativeDenom R ≤ R.maximalIdeal :=
  sorry

/-- The `Λ`-submodule of `maximalIdeal R.carrier` cut out by `relativeDenom R`. -/
def relativeSubmodule (R : CompleteLocalAlgCat Λ k) :
    Submodule Λ R.maximalIdeal :=
  (Submodule.comap R.maximalIdeal.subtype (relativeDenom R)).restrictScalars Λ

/-- Membership in `relativeSubmodule R` is membership of the underlying element in
`relativeDenom R`. -/
theorem mem_relativeSubmodule {R : CompleteLocalAlgCat Λ k} {x : R.maximalIdeal} :
    x ∈ relativeSubmodule R ↔ (x : R.carrier) ∈ relativeDenom R :=
  Iff.rfl

namespace Hom

/-- The restriction of a morphism in `CompleteLocalAlgCat` to maximal ideals. -/
def mapMaximalIdeal {R S : CompleteLocalAlgCat Λ k} (f : Hom R S) :
    R.maximalIdeal →ₗ[Λ] S.maximalIdeal where
  toFun x :=
    ⟨f.hom (x : R.carrier),
      (maximalIdeal_comap (f.hom : R.carrier →+* S.carrier)).symm.le x.2⟩
  map_add' x y := Subtype.ext (map_add f.hom (x : R.carrier) (y : R.carrier))
  map_smul' r x :=
    Subtype.ext (LinearMap.map_smul f.hom.toLinearMap r (x : R.carrier))

/-- The maximal-ideal restriction of a morphism applies as the underlying algebra map. -/
theorem mapMaximalIdeal_apply {R S : CompleteLocalAlgCat Λ k} (f : Hom R S)
    (x : R.maximalIdeal) :
    mapMaximalIdeal f x =
      ⟨f.hom (x : R.carrier),
        (maximalIdeal_comap (f.hom : R.carrier →+* S.carrier)).symm.le x.2⟩ :=
  rfl

/-- A morphism in `CompleteLocalAlgCat` sends `relativeSubmodule` into the target
`relativeSubmodule`. -/
theorem relativeSubmodule_map_le {R S : CompleteLocalAlgCat Λ k} (f : Hom R S) :
    relativeSubmodule R ≤ (relativeSubmodule S).comap (mapMaximalIdeal f) :=
  sorry

/-- The `Λ`-linear map of relative quotients `maximalIdeal ⧸ relativeSubmodule` induced by a
morphism in `CompleteLocalAlgCat`. -/
def mapRelative {R S : CompleteLocalAlgCat Λ k} (f : Hom R S) :
    (R.maximalIdeal ⧸ relativeSubmodule R) →ₗ[Λ]
      (S.maximalIdeal ⧸ relativeSubmodule S) :=
  Submodule.mapQ (relativeSubmodule R) (relativeSubmodule S) (mapMaximalIdeal f)
    (relativeSubmodule_map_le f)

/-- The relative quotient map sends the class of an element of the maximal ideal to the class
of its image. -/
theorem mapRelative_mk {R S : CompleteLocalAlgCat Λ k} (f : Hom R S)
    (x : R.maximalIdeal) :
    mapRelative f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        ⟨f.hom (x : R.carrier),
          (maximalIdeal_comap (f.hom : R.carrier →+* S.carrier)).symm.le x.2⟩ :=
  rfl

/-- A residue-compatible complete local algebra morphism is surjective if and only if its
induced map on cotangent spaces is surjective. -/
theorem surjective_iff_mapAlgHom {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    Function.Surjective f.hom ↔ Function.Surjective (CotangentSpace.mapAlgHom f.hom) :=
  sorry

/-- The ordinary cotangent map of a residue-compatible complete local algebra morphism is
surjective if and only if its relative cotangent quotient map is surjective. -/
theorem mapAlgHom_surjective_iff_mapRelative {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    Function.Surjective (CotangentSpace.mapAlgHom f.hom) ↔
      Function.Surjective (mapRelative f) :=
  sorry

/-- A residue-compatible complete local algebra morphism is surjective if and only if its
relative cotangent quotient map is surjective. -/
theorem surjective_iff_mapRelative {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    Function.Surjective f.hom ↔ Function.Surjective (mapRelative f) :=
  sorry

end Hom

end CompleteLocalAlgCat
