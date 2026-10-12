/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import stacks_project.Chap88.Definition_88_20_1_Comparison

/-!
# Affine morphisms induced by surjections whose kernel cotangent is annihilated
by an ideal of definition

A morphism of affine formal algebraic spaces corresponds to a surjective
homomorphism `φ : A →+* B` of adic Noetherian rings whose kernel `J` has
`I • J.Cotangent = ⊥` for some ideal of definition `I` of `A`. The
correspondence is contravariant: `φ` induces a map from the thickening of `B`
to the thickening of `A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace TopologicalRing.Ideal

/-- An ideal `J` has cotangent annihilated by an ideal of definition if there
exists an ideal of definition `I` with `I • (⊤ : Submodule A J.Cotangent) = ⊥`.
This encodes `I (J / J ^ 2) = 0`. -/
def IsCotangentAnnihilatedByIdealOfDefinition {A : Type u} [CommRing A]
    [TopologicalSpace A] (J : Ideal A) : Prop :=
  ∃ I : Ideal A, IsIdealOfDefinition I ∧ I • (⊤ : Submodule A J.Cotangent) = ⊥

/-- An ideal has cotangent annihilated by an ideal of definition if and only if
there exists an ideal of definition `I` with
`I • (⊤ : Submodule A J.Cotangent) = ⊥`. -/
theorem isCotangentAnnihilatedByIdealOfDefinition_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] (J : Ideal A) :
    IsCotangentAnnihilatedByIdealOfDefinition J ↔
      ∃ I : Ideal A, IsIdealOfDefinition I ∧
        I • (⊤ : Submodule A J.Cotangent) = ⊥ :=
  sorry

namespace IsCotangentAnnihilatedByIdealOfDefinition

/-- If `I` is an ideal of definition and `I` annihilates `J.Cotangent`, then
`J` has cotangent annihilated by an ideal of definition. -/
theorem of_smul {A : Type u} [CommRing A] [TopologicalSpace A] {J I : Ideal A}
    (hI : IsIdealOfDefinition I)
    (h : I • (⊤ : Submodule A J.Cotangent) = ⊥) :
    IsCotangentAnnihilatedByIdealOfDefinition J :=
  sorry

/-- If `J` has cotangent annihilated by an ideal of definition, there exists an
ideal of definition `I` with `I • (⊤ : Submodule A J.Cotangent) = ⊥`. -/
theorem spec {A : Type u} [CommRing A] [TopologicalSpace A] {J : Ideal A}
    (h : IsCotangentAnnihilatedByIdealOfDefinition J) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧
      I • (⊤ : Submodule A J.Cotangent) = ⊥ :=
  sorry

end IsCotangentAnnihilatedByIdealOfDefinition

end TopologicalRing.Ideal

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A morphism of affine formal algebraic spaces corresponds to a surjection in
the category of adic Noetherian rings whose kernel cotangent is annihilated by
an ideal of definition, when it is induced by a surjective homomorphism
`φ : A →+* B` with
`IsCotangentAnnihilatedByIdealOfDefinition (RingHom.ker φ)`.

Here `φ : A →+* B` induces `g : U ⟶ V` with `U` presented by `B` and `V`
presented by `A`. Thus the Stacks map `B → A` is this `φ`, the Stacks kernel
`J` is `RingHom.ker φ ⊆ A`, and the Stacks ideal of definition `I ⊂ B` is an
ideal of definition of `A`. -/
class KernelCotangentAnnihilatedByIdealOfDefinition {S : Scheme.{u}}
    {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) : Prop where
  /-- There is a surjective homomorphism of adic Noetherian rings inducing `g`
  whose kernel cotangent is annihilated by some ideal of definition. -/
  exists_hom :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        Function.Surjective φ ∧
          TopologicalRing.Ideal.IsCotangentAnnihilatedByIdealOfDefinition
              (RingHom.ker φ) ∧
            IsInducedBy g φ

namespace KernelCotangentAnnihilatedByIdealOfDefinition

/-- The identity of a Noetherian affine formal algebraic space corresponds to a
surjection of adic Noetherian rings whose kernel cotangent is annihilated by an
ideal of definition. -/
instance id {S : Scheme.{u}} {U : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsNoetherianAffine U] :
    KernelCotangentAnnihilatedByIdealOfDefinition (𝟙 U) :=
  sorry

/-- A morphism induced by a surjective homomorphism of adic Noetherian rings
whose kernel cotangent is annihilated by an ideal of definition has
`KernelCotangentAnnihilatedByIdealOfDefinition`. -/
theorem ofHom {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B)
    (hφ : Function.Surjective φ)
    (hker :
      TopologicalRing.Ideal.IsCotangentAnnihilatedByIdealOfDefinition
        (RingHom.ker φ))
    (hg : IsInducedBy g φ) :
    KernelCotangentAnnihilatedByIdealOfDefinition g :=
  sorry

/-- A morphism with `KernelCotangentAnnihilatedByIdealOfDefinition` is induced
by a surjective homomorphism of adic Noetherian rings whose kernel cotangent is
annihilated by an ideal of definition. -/
theorem spec {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) [KernelCotangentAnnihilatedByIdealOfDefinition g] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        Function.Surjective φ ∧
          TopologicalRing.Ideal.IsCotangentAnnihilatedByIdealOfDefinition
              (RingHom.ker φ) ∧
            IsInducedBy g φ :=
  sorry

/-- `KernelCotangentAnnihilatedByIdealOfDefinition g` if and only if `g` is
induced by a surjective homomorphism of adic Noetherian rings whose kernel
cotangent is annihilated by an ideal of definition. -/
theorem iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) :
    KernelCotangentAnnihilatedByIdealOfDefinition g ↔
      ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
        (_ : TopologicalSpace A) (_ : TopologicalSpace B)
        (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
        (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
        (φ : A →+* B),
          Function.Surjective φ ∧
            TopologicalRing.Ideal.IsCotangentAnnihilatedByIdealOfDefinition
                (RingHom.ker φ) ∧
              IsInducedBy g φ :=
  sorry

end KernelCotangentAnnihilatedByIdealOfDefinition

end AlgebraicGeometry.AffineFormalAlgebraicSpace
