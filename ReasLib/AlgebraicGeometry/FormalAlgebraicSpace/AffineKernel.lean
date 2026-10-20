/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Annihilation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineMorphism
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineTypes

/-!
# Surjective affine presentations with annihilated kernel powers
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- An arrow of presheaves over a scheme is induced by a surjective homomorphism
of adic Noetherian rings whose kernel has a positive power annihilated by an
ideal of definition. For `φ : A →+* B` inducing `g : U ⟶ V`, the kernel and
its annihilating ideal of definition lie in `A`, which presents `V`. -/
class KernelKilledByPowIdealOfDefinition {S : Scheme.{u}}
    {U V : (Over S)ᵒᵖ ⥤ Type u}
    (g : U ⟶ V) : Prop where
  /-- There is a surjective homomorphism of adic Noetherian rings inducing `g`
  whose kernel has a positive power annihilated by an ideal of definition. -/
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
surjection of adic Noetherian rings whose kernel has a positive power
annihilated by an ideal of definition. -/
instance id {S : Scheme.{u}} {U : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsNoetherianAffine U] :
    KernelKilledByPowIdealOfDefinition (𝟙 U) :=
  sorry

/-- A morphism induced by a surjective homomorphism of adic Noetherian rings
whose kernel has a positive power annihilated by an ideal of definition has
`KernelKilledByPowIdealOfDefinition`. -/
theorem ofHom {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (g : U ⟶ V) {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B)
    (hφ : Function.Surjective φ)
    (hker : TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition (RingHom.ker φ))
    (hg : IsInducedBy g φ) : KernelKilledByPowIdealOfDefinition g :=
  ⟨⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, φ, hφ, hker, hg⟩⟩

/-- A morphism with `KernelKilledByPowIdealOfDefinition` is induced by a
surjective homomorphism of adic Noetherian rings whose kernel has a positive
power annihilated by an ideal of definition. -/
theorem spec {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (g : U ⟶ V) [KernelKilledByPowIdealOfDefinition g] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        Function.Surjective φ ∧
          TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition (RingHom.ker φ) ∧
            IsInducedBy g φ :=
  KernelKilledByPowIdealOfDefinition.exists_hom

/-- `KernelKilledByPowIdealOfDefinition g` if and only if `g` is induced by a
surjective homomorphism of adic Noetherian rings whose kernel has a positive
power annihilated by an ideal of definition. -/
theorem iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
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
  ⟨fun h ↦ h.exists_hom, fun h ↦ ⟨h⟩⟩

end KernelKilledByPowIdealOfDefinition

/-- An arrow of presheaves over a scheme is induced by a surjective homomorphism
of adic Noetherian rings whose kernel is annihilated by an ideal of definition.
For `φ : A →+* B` inducing `g : U ⟶ V`, the kernel and its annihilating ideal
of definition lie in `A`, which presents `V`. -/
class KernelKilledByIdealOfDefinition {S : Scheme.{u}}
    {U V : (Over S)ᵒᵖ ⥤ Type u}
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
    (g : U ⟶ V) {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B)
    (hφ : Function.Surjective φ)
    (hker : TopologicalRing.Ideal.IsKilledByIdealOfDefinition (RingHom.ker φ))
    (hg : IsInducedBy g φ) : KernelKilledByIdealOfDefinition g :=
  ⟨⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, φ, hφ, hker, hg⟩⟩

/-- A morphism with `KernelKilledByIdealOfDefinition` is induced by a
surjective homomorphism of adic Noetherian rings whose kernel is killed by an
ideal of definition. -/
theorem spec {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (g : U ⟶ V) [KernelKilledByIdealOfDefinition g] :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        Function.Surjective φ ∧
          TopologicalRing.Ideal.IsKilledByIdealOfDefinition (RingHom.ker φ) ∧
            IsInducedBy g φ :=
  KernelKilledByIdealOfDefinition.exists_hom

/-- `KernelKilledByIdealOfDefinition g` if and only if `g` is induced by a
surjective homomorphism of adic Noetherian rings whose kernel is killed by an
ideal of definition. -/
theorem iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
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
  ⟨fun h ↦ h.exists_hom, fun h ↦ ⟨h⟩⟩

end KernelKilledByIdealOfDefinition

end AlgebraicGeometry.AffineFormalAlgebraicSpace
