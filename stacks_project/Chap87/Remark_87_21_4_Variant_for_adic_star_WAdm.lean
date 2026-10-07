module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap87.Definition_87_23_2
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star_AdicStarRing

/-!
# WAdm^{adic*} correspondence for morphisms of affine formal algebraic spaces

A morphism of affine formal algebraic spaces over `S` corresponds to a morphism
of `WAdm^{adic*}` with property `P` when some adic* presentations identify it
with `Spf(φ)` for a continuous ring map `φ` satisfying `P`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

noncomputable section

universe u v

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B],
    (B →+* A) → Prop)

/-- A morphism of affine formal algebraic spaces corresponds to a morphism of
`WAdm^{adic*}` with property `P` when there are adic* presentations of source
and target, together with a continuous ring map `φ` satisfying `P`, such that
`f` is identified with `Spf(φ)` on adic power stages. -/
def correspondsTo {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : U ⟶ V) : Prop :=
  ∃ (A B : Type u)
    (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicStarRing A)
    (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsAdicStarRing B)
    (φ : B →+* A) (_ : Continuous φ) (I : Ideal A) (J : Ideal B),
    P φ ∧ IsColimitMapOf φ I J f

/-- `correspondsTo P f` unpacks as adic* presentations of the affine source and
target together with a continuous ring map `φ` satisfying `P` that induces `f`
on adic power stages. -/
theorem correspondsTo_iff {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : U ⟶ V) :
    correspondsTo P f ↔
      ∃ (A B : Type u)
        (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicStarRing A)
        (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsAdicStarRing B)
        (φ : B →+* A) (_ : Continuous φ) (I : Ideal A) (J : Ideal B),
        P φ ∧ IsColimitMapOf φ I J f := sorry

namespace correspondsTo

variable {P}

/-- A continuous ring map `φ` with `P φ`, together with compatible `Spf`
presentations of the affine source and target, witnesses `correspondsTo P f`. -/
theorem of {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : U ⟶ V}
    {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
    (φ : B →+* A) (hφ : Continuous φ) (I : Ideal A) (J : Ideal B)
    (hPφ : P φ) (hinduces : IsColimitMapOf φ I J f) :
    correspondsTo P f := sorry

/-- `correspondsTo P f` supplies adic* presentations and a continuous ring map
`φ` with `P φ` inducing `f`. -/
theorem spec {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : U ⟶ V}
    (h : correspondsTo P f) :
    ∃ (A B : Type u)
      (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsAdicStarRing A)
      (_ : CommRing B) (_ : TopologicalSpace B) (_ : IsAdicStarRing B)
      (φ : B →+* A) (_ : Continuous φ) (I : Ideal A) (J : Ideal B),
      P φ ∧ IsColimitMapOf φ I J f := sorry

end correspondsTo

end AlgebraicGeometry.IsLocallyAdicStar
