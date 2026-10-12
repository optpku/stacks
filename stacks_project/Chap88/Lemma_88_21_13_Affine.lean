/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Definition_88_20_1_Comparison
public import stacks_project.Chap88.Lemma_88_21_12_Affine

/-!
# Affine morphisms induced by surjections with kernel killed by an ideal of definition

A morphism of affine formal algebraic spaces corresponds to a surjective
homomorphism `φ : A →+* B` of adic Noetherian rings whose kernel is killed by
an ideal of definition of `A`. The correspondence is contravariant: `φ`
induces a map from the thickening of `B` to the thickening of `A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace TopologicalRing.Ideal

/-- An ideal `J` is killed by an ideal of definition if there exists an ideal
of definition `I` with `I * J = ⊥`. -/
def IsKilledByIdealOfDefinition {A : Type u} [CommRing A] [TopologicalSpace A]
    (J : Ideal A) : Prop :=
  ∃ I : Ideal A, IsIdealOfDefinition I ∧ I * J = ⊥

/-- An ideal is killed by an ideal of definition if and only if there exists an
ideal of definition `I` with `I * J = ⊥`. -/
theorem isKilledByIdealOfDefinition_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] (J : Ideal A) :
    IsKilledByIdealOfDefinition J ↔
      ∃ I : Ideal A, IsIdealOfDefinition I ∧ I * J = ⊥ :=
  sorry

namespace IsKilledByIdealOfDefinition

/-- If `I` is an ideal of definition and `I * J = ⊥`, then `J` is killed by an
ideal of definition. -/
theorem of_mul {A : Type u} [CommRing A] [TopologicalSpace A] {J I : Ideal A}
    (hI : IsIdealOfDefinition I) (h : I * J = ⊥) :
    IsKilledByIdealOfDefinition J :=
  sorry

/-- If `J` is killed by an ideal of definition, there exists an ideal of
definition `I` with `I * J = ⊥`. -/
theorem spec {A : Type u} [CommRing A] [TopologicalSpace A] {J : Ideal A}
    (h : IsKilledByIdealOfDefinition J) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ I * J = ⊥ :=
  sorry

/-- If `J` is killed by an ideal of definition, then it is killed by a power of
an ideal of definition. -/
theorem to_isKilledByPowIdealOfDefinition {A : Type u} [CommRing A]
    [TopologicalSpace A] {J : Ideal A} (h : IsKilledByIdealOfDefinition J) :
    IsKilledByPowIdealOfDefinition J :=
  sorry

end IsKilledByIdealOfDefinition

end TopologicalRing.Ideal

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A morphism of affine formal algebraic spaces corresponds to a surjection in
the category of adic Noetherian rings whose kernel is killed by an ideal of
definition, when it is induced by a surjective homomorphism `φ : A →+* B` with
`IsKilledByIdealOfDefinition (RingHom.ker φ)`.

Here `φ : A →+* B` induces `g : U ⟶ V` with `U` presented by `B` and `V`
presented by `A`. Thus the Stacks map `B → A` is this `φ`, the Stacks kernel
`J` is `RingHom.ker φ ⊆ A`, and the Stacks ideal of definition `I ⊂ B` is an
ideal of definition of `A`. -/
class KernelKilledByIdealOfDefinition {S : Scheme.{u}}
    {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) : Prop where
  /-- There is a surjective homomorphism of adic Noetherian rings inducing `g`
  whose kernel is killed by an ideal of definition. -/
  exists_hom :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        Function.Surjective φ ∧
          TopologicalRing.Ideal.IsKilledByIdealOfDefinition (RingHom.ker φ) ∧
            IsInducedBy g φ

namespace KernelKilledByIdealOfDefinition

/-- The identity of a Noetherian affine formal algebraic space corresponds to a
surjection of adic Noetherian rings whose kernel is killed by an ideal of
definition. -/
instance id {S : Scheme.{u}} {U : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsNoetherianAffine U] :
    KernelKilledByIdealOfDefinition (𝟙 U) :=
  sorry

/-- A morphism induced by a surjective homomorphism of adic Noetherian rings
whose kernel is killed by an ideal of definition has
`KernelKilledByIdealOfDefinition`. -/
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
    (hker : TopologicalRing.Ideal.IsKilledByIdealOfDefinition (RingHom.ker φ))
    (hg : IsInducedBy g φ) : KernelKilledByIdealOfDefinition g :=
  sorry

/-- A morphism with `KernelKilledByIdealOfDefinition` is induced by a
surjective homomorphism of adic Noetherian rings whose kernel is killed by an
ideal of definition. -/
theorem spec {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) [KernelKilledByIdealOfDefinition g] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        Function.Surjective φ ∧
          TopologicalRing.Ideal.IsKilledByIdealOfDefinition (RingHom.ker φ) ∧
            IsInducedBy g φ :=
  sorry

/-- `KernelKilledByIdealOfDefinition g` if and only if `g` is induced by a
surjective homomorphism of adic Noetherian rings whose kernel is killed by an
ideal of definition. -/
theorem iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) :
    KernelKilledByIdealOfDefinition g ↔
      ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
        (_ : TopologicalSpace A) (_ : TopologicalSpace B)
        (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
        (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
        (φ : A →+* B),
          Function.Surjective φ ∧
            TopologicalRing.Ideal.IsKilledByIdealOfDefinition (RingHom.ker φ) ∧
              IsInducedBy g φ :=
  sorry

end KernelKilledByIdealOfDefinition

end AlgebraicGeometry.AffineFormalAlgebraicSpace
