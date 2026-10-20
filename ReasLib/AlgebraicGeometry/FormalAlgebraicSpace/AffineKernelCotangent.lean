/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Cotangent
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineMorphism
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineTypes

/-!
# Surjective affine presentations with annihilated kernel cotangent
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- An arrow of presheaves over a scheme is induced by a surjective homomorphism
of adic Noetherian rings whose kernel cotangent is annihilated by an ideal of
definition. For `φ : A →+* B` inducing `g : U ⟶ V`, the kernel and its
annihilating ideal of definition lie in `A`, which presents `V`, while `B`
presents `U`. -/
class KernelCotangentAnnihilatedByIdealOfDefinition {S : Scheme.{u}}
    {U V : (Over S)ᵒᵖ ⥤ Type u}
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
  ⟨⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, φ, hφ, hker, hg⟩⟩

/-- A morphism with `KernelCotangentAnnihilatedByIdealOfDefinition` is induced
by a surjective homomorphism of adic Noetherian rings whose kernel cotangent is
annihilated by an ideal of definition. -/
theorem spec {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
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
  KernelCotangentAnnihilatedByIdealOfDefinition.exists_hom

/-- `KernelCotangentAnnihilatedByIdealOfDefinition g` if and only if `g` is
induced by a surjective homomorphism of adic Noetherian rings whose kernel
cotangent is annihilated by an ideal of definition. -/
theorem iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
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
  ⟨fun h ↦ h.exists_hom, fun h ↦ ⟨h⟩⟩

end KernelCotangentAnnihilatedByIdealOfDefinition

end AlgebraicGeometry.AffineFormalAlgebraicSpace
