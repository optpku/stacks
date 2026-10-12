/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal

/-!
# Relative-cotangent maps along morphisms in `Ĉ_Λ`

Morphisms in `CompleteLocalAlgCat Λ k` induce maps of the relative quotients
`maximalIdeal ⧸ (m_Λ · (-) + maximalIdeal ^ 2)`, where `m_Λ` is
`RingHom.ker (algebraMap Λ k)`.
-/

@[expose] public section

open IsLocalRing

universe u

namespace CompleteLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The ideal `m_Λ R + m_R²`, where `m_Λ` is `RingHom.ker (algebraMap Λ k)`. -/
def relativeDenom (R : CompleteLocalAlgCat Λ k) : Ideal R.carrier :=
  (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ R.carrier) ⊔ maximalIdeal R.carrier ^ 2

/-- `relativeDenom R` is the sum of the extension of `ker (algebraMap Λ k)` and the square of
the maximal ideal. -/
theorem relativeDenom_spec (R : CompleteLocalAlgCat Λ k) :
    relativeDenom R =
      (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ R.carrier) ⊔
        maximalIdeal R.carrier ^ 2 :=
  rfl

/-- The relative denominator `m_Λ R + m_R²` is contained in the maximal ideal. -/
theorem relativeDenom_le_maximalIdeal (R : CompleteLocalAlgCat Λ k) :
    relativeDenom R ≤ maximalIdeal R.carrier :=
  sorry

/-- The `Λ`-submodule of `maximalIdeal R.carrier` cut out by `relativeDenom R`. -/
def relativeSubmodule (R : CompleteLocalAlgCat Λ k) :
    Submodule Λ (maximalIdeal R.carrier) :=
  (Submodule.comap (maximalIdeal R.carrier).subtype (relativeDenom R)).restrictScalars Λ

/-- Membership in `relativeSubmodule R` is membership of the underlying element in
`relativeDenom R`. -/
theorem mem_relativeSubmodule {R : CompleteLocalAlgCat Λ k} {x : maximalIdeal R.carrier} :
    x ∈ relativeSubmodule R ↔ (x : R.carrier) ∈ relativeDenom R :=
  Iff.rfl

namespace Hom

/-- The restriction of a morphism in `CompleteLocalAlgCat` to maximal ideals. -/
def mapMaximalIdeal {R S : CompleteLocalAlgCat Λ k} (f : Hom R S) :
    maximalIdeal R.carrier →ₗ[Λ] maximalIdeal S.carrier where
  toFun x :=
    ⟨f.hom (x : R.carrier),
      (maximalIdeal_comap (f.hom : R.carrier →+* S.carrier)).symm.le x.2⟩
  map_add' x y := Subtype.ext (map_add f.hom (x : R.carrier) (y : R.carrier))
  map_smul' r x :=
    Subtype.ext (LinearMap.map_smul f.hom.toLinearMap r (x : R.carrier))

/-- The maximal-ideal restriction of a morphism applies as the underlying algebra map. -/
theorem mapMaximalIdeal_apply {R S : CompleteLocalAlgCat Λ k} (f : Hom R S)
    (x : maximalIdeal R.carrier) :
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
    (maximalIdeal R.carrier ⧸ relativeSubmodule R) →ₗ[Λ]
      (maximalIdeal S.carrier ⧸ relativeSubmodule S) :=
  Submodule.mapQ (relativeSubmodule R) (relativeSubmodule S) (mapMaximalIdeal f)
    (relativeSubmodule_map_le f)

/-- The relative quotient map sends the class of an element of the maximal ideal to the class
of its image. -/
theorem mapRelative_mk {R S : CompleteLocalAlgCat Λ k} (f : Hom R S)
    (x : maximalIdeal R.carrier) :
    mapRelative f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        ⟨f.hom (x : R.carrier),
          (maximalIdeal_comap (f.hom : R.carrier →+* S.carrier)).symm.le x.2⟩ :=
  rfl

end Hom

end CompleteLocalAlgCat
