module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The first extension group of the naive cotangent complex

The self-presentation of an algebra gives the explicit cokernel model used for
first extension classes of its naive cotangent complex.
-/

@[expose] public section

noncomputable section

universe u

open Algebra Algebra.Generators Algebra.Extension

namespace RingHom.SquareZeroExtension

variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- The cokernel model for Ext¹ of the naive cotangent complex. -/
abbrev extOneNaiveCotangent : Type u :=
  let P := (Generators.self A B).toExtension
  (P.Cotangent →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N P.cotangentComplex)

/-- The quotient class of a linear map from the conormal module. -/
def extOneNaiveCotangent_mk
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    extOneNaiveCotangent A B N :=
  Submodule.Quotient.mk f

/-- A conormal class vanishes exactly when its representative factors through the cotangent differential. -/
theorem extOneNaiveCotangent_eq_zero_iff
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    extOneNaiveCotangent_mk A B N f = 0 ↔
      ∃ g : (Generators.self A B).toExtension.CotangentSpace →ₗ[B] N,
        f = g ∘ₗ (Generators.self A B).toExtension.cotangentComplex := sorry

/-! Presentation-level models for the first extension group. -/

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- Ext¹ of the naive cotangent complex associated to a polynomial presentation. -/
abbrev extOneOf {ι : Type u} (G : Algebra.Generators A B ι) (N : Type u)
    [AddCommGroup N] [Module B N] : Type u :=
  (G.toExtension.Cotangent →ₗ[B] N) ⧸
    LinearMap.range (LinearMap.lcomp B N G.toExtension.cotangentComplex)

/-- The quotient class of a map from the conormal module. -/
def extOneOf_mk {ι : Type u} (G : Algebra.Generators A B ι) (N : Type u)
    [AddCommGroup N] [Module B N]
    (f : G.toExtension.Cotangent →ₗ[B] N) : extOneOf G N :=
  Submodule.Quotient.mk f

/-- The presentation-level model agrees with the self-presentation model. -/
theorem extOneOf_self (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module B N] :
    extOneOf (Generators.self A B) N = extOneNaiveCotangent A B N := sorry

/-- Comparison from a presentation-level Ext model to the self-presentation model. -/
def compareToSelf {ι : Type u} (G : Algebra.Generators A B ι) (N : Type u)
    [AddCommGroup N] [Module B N] :
    extOneOf G N →+ extOneNaiveCotangent A B N :=
  (Submodule.mapQ
      (LinearMap.range (LinearMap.lcomp B N G.toExtension.cotangentComplex))
      (LinearMap.range (LinearMap.lcomp B N
        (Generators.self A B).toExtension.cotangentComplex))
      (LinearMap.lcomp B N
        (Cotangent.map (Algebra.Extension.defaultHom A B G.toExtension)))
      sorry).toAddMonoidHom

/-- The comparison map on quotient representatives. -/
theorem compareToSelf_mk {ι : Type u} (G : Algebra.Generators A B ι) (N : Type u)
    [AddCommGroup N] [Module B N]
    (f : G.toExtension.Cotangent →ₗ[B] N) :
    compareToSelf G N (extOneOf_mk G N f) =
      extOneNaiveCotangent_mk A B N
        (f ∘ₗ Cotangent.map (Algebra.Extension.defaultHom A B G.toExtension)) := sorry

/-- The arbitrary-presentation Ext class vanishes exactly when it factors through
the presentation cotangent differential. -/
theorem extOneOf_eq_zero_iff {ι : Type u} (G : Algebra.Generators A B ι)
    (f : G.toExtension.Cotangent →ₗ[B] N) :
    extOneOf_mk G N f = 0 ↔
      ∃ g : G.toExtension.CotangentSpace →ₗ[B] N,
        f = g ∘ₗ G.toExtension.cotangentComplex := sorry

end RingHom.SquareZeroExtension
