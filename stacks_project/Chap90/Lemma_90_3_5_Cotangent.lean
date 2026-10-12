/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Cotangent and relative-cotangent maps along morphisms in `C_Λ`

Local algebra homomorphisms induce maps of cotangent spaces. In the base category
`ArtinianLocalAlgCat Λ k`, they also induce maps of the relative quotients
`maximalIdeal ⧸ (m_Λ · (-) + maximalIdeal ^ 2)`, where `m_Λ` is
`RingHom.ker (algebraMap Λ k)`.
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace IsLocalRing.CotangentSpace

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [Algebra R A] [Algebra R B]

/-- The map of cotangent spaces induced by a local algebra homomorphism. -/
def mapAlgHom (f : A →ₐ[R] B) [IsLocalHom f] :
    CotangentSpace A →ₗ[R] CotangentSpace B :=
  Ideal.mapCotangent (maximalIdeal A) (maximalIdeal B) f
    (maximalIdeal_comap (f : A →+* B)).symm.le

/-- The induced cotangent map sends the class of an element of the maximal ideal to the
class of its image. -/
@[simp]
theorem mapAlgHom_toCotangent (f : A →ₐ[R] B) [IsLocalHom f] (x : maximalIdeal A) :
    mapAlgHom f ((maximalIdeal A).toCotangent x) =
      (maximalIdeal B).toCotangent ⟨f x, (maximalIdeal_comap (f : A →+* B)).symm.le x.2⟩ :=
  rfl

end IsLocalRing.CotangentSpace

namespace ArtinianLocalAlgCat

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

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
    relativeDenom A ≤ maximalIdeal A.carrier :=
  sorry

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
    relativeSubmodule A ≤ (relativeSubmodule B).comap (mapMaximalIdeal f) :=
  sorry

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

end Hom

end ArtinianLocalAlgCat
