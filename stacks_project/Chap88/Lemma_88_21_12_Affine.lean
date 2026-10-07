module

public import stacks_project.Chap88.Definition_88_20_1_Comparison

/-!
# Affine morphisms induced by surjections with kernel killed by a power of an ideal of definition

A morphism of affine formal algebraic spaces corresponds to a surjective
homomorphism `φ : A →+* B` of adic Noetherian rings whose kernel is killed by
a power of an ideal of definition of `A`. The correspondence is contravariant:
`φ` induces a map from the thickening of `B` to the thickening of `A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace TopologicalRing.Ideal

/-- An ideal `J` is killed by a power of an ideal of definition if there exist
an ideal of definition `I` and a positive integer `n` with `I * J ^ n = ⊥`. -/
def IsKilledByPowIdealOfDefinition {A : Type u} [CommRing A] [TopologicalSpace A]
    (J : Ideal A) : Prop :=
  ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∃ n : ℕ, 0 < n ∧ I * J ^ n = ⊥

/-- An ideal is killed by a power of an ideal of definition if and only if there
exist an ideal of definition `I` and a positive integer `n` with
`I * J ^ n = ⊥`. -/
theorem isKilledByPowIdealOfDefinition_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] (J : Ideal A) :
    IsKilledByPowIdealOfDefinition J ↔
      ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∃ n : ℕ, 0 < n ∧ I * J ^ n = ⊥ :=
  sorry

namespace IsKilledByPowIdealOfDefinition

/-- If `I` is an ideal of definition and `I * J ^ n = ⊥` for some positive
integer `n`, then `J` is killed by a power of an ideal of definition. -/
theorem of_mul_pow {A : Type u} [CommRing A] [TopologicalSpace A] {J I : Ideal A}
    (hI : IsIdealOfDefinition I) (n : ℕ) (hn : 0 < n) (h : I * J ^ n = ⊥) :
    IsKilledByPowIdealOfDefinition J :=
  sorry

/-- If `I` is an ideal of definition and `I * J = ⊥`, then `J` is killed by a
power of an ideal of definition. -/
theorem of_mul {A : Type u} [CommRing A] [TopologicalSpace A] {J I : Ideal A}
    (hI : IsIdealOfDefinition I) (h : I * J = ⊥) :
    IsKilledByPowIdealOfDefinition J :=
  sorry

/-- If `J` is killed by a power of an ideal of definition, there exist an ideal
of definition `I` and a positive integer `n` with `I * J ^ n = ⊥`. -/
theorem spec {A : Type u} [CommRing A] [TopologicalSpace A] {J : Ideal A}
    (h : IsKilledByPowIdealOfDefinition J) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∃ n : ℕ, 0 < n ∧ I * J ^ n = ⊥ :=
  sorry

end IsKilledByPowIdealOfDefinition

end TopologicalRing.Ideal

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A morphism of affine formal algebraic spaces corresponds to a surjection in
the category of adic Noetherian rings whose kernel is killed by a power of an
ideal of definition, when it is induced by a surjective homomorphism
`φ : A →+* B` with `IsKilledByPowIdealOfDefinition (RingHom.ker φ)`.

Here `φ : A →+* B` induces `g : U ⟶ V` with `U` presented by `B` and `V`
presented by `A`. Thus the Stacks map `B → A` is this `φ`, the Stacks kernel
`J` is `RingHom.ker φ ⊆ A`, and the Stacks ideal of definition `I ⊂ B` is an
ideal of definition of `A`. -/
class KernelKilledByPowIdealOfDefinition {S : Scheme.{u}}
    {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) : Prop where
  /-- There is a surjective homomorphism of adic Noetherian rings inducing `g`
  whose kernel is killed by a power of an ideal of definition. -/
  exists_hom :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        Function.Surjective φ ∧
          TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition (RingHom.ker φ) ∧
            IsInducedBy g φ

namespace KernelKilledByPowIdealOfDefinition

/-- The identity of a Noetherian affine formal algebraic space corresponds to a
surjection of adic Noetherian rings whose kernel is killed by a power of an
ideal of definition. -/
instance id {S : Scheme.{u}} {U : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsNoetherianAffine U] :
    KernelKilledByPowIdealOfDefinition (𝟙 U) :=
  sorry

/-- A morphism induced by a surjective homomorphism of adic Noetherian rings
whose kernel is killed by a power of an ideal of definition has
`KernelKilledByPowIdealOfDefinition`. -/
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
    (hker : TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition (RingHom.ker φ))
    (hg : IsInducedBy g φ) : KernelKilledByPowIdealOfDefinition g :=
  sorry

/-- A morphism with `KernelKilledByPowIdealOfDefinition` is induced by a
surjective homomorphism of adic Noetherian rings whose kernel is killed by a
power of an ideal of definition. -/
theorem spec {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) [KernelKilledByPowIdealOfDefinition g] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        Function.Surjective φ ∧
          TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition (RingHom.ker φ) ∧
            IsInducedBy g φ :=
  sorry

/-- `KernelKilledByPowIdealOfDefinition g` if and only if `g` is induced by a
surjective homomorphism of adic Noetherian rings whose kernel is killed by a
power of an ideal of definition. -/
theorem iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V]
    (g : U ⟶ V) :
    KernelKilledByPowIdealOfDefinition g ↔
      ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
        (_ : TopologicalSpace A) (_ : TopologicalSpace B)
        (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
        (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
        (φ : A →+* B),
          Function.Surjective φ ∧
            TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition (RingHom.ker φ) ∧
              IsInducedBy g φ :=
  sorry

end KernelKilledByPowIdealOfDefinition

end AlgebraicGeometry.AffineFormalAlgebraicSpace
