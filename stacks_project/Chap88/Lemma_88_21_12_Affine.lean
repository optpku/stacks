module

public import ReasLib.RingTheory.Topology.Adic.Annihilation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineKernel

/-!
# Affine kernel and ideal annihilation APIs

The exported ideal and affine kernel criteria are provided by their mathematical owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace TopologicalRing.Ideal

universe u

#check (TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
    (J : Ideal A),
    Prop)

#check (TopologicalRing.Ideal.isKilledByPowIdealOfDefinition_iff :
  ∀ {A : Type u} [CommRing A]
    [TopologicalSpace A] (J : Ideal A),
    IsKilledByPowIdealOfDefinition J ↔
      ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∃ n : ℕ, 0 < n ∧ I * J ^ n = ⊥)

#check (TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition.of_mul_pow :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] {J I : Ideal A}
    (hI : IsIdealOfDefinition I) (n : ℕ) (hn : 0 < n) (h : I * J ^ n = ⊥),
    IsKilledByPowIdealOfDefinition J)

#check (TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition.of_mul :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] {J I : Ideal A}
    (hI : IsIdealOfDefinition I) (h : I * J = ⊥),
    IsKilledByPowIdealOfDefinition J)

#check (TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition.spec :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] {J : Ideal A}
    (h : IsKilledByPowIdealOfDefinition J),
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∃ n : ℕ, 0 < n ∧ I * J ^ n = ⊥)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.KernelKilledByPowIdealOfDefinition :
  ∀ {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}, (U ⟶ V) → Prop)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.KernelKilledByPowIdealOfDefinition.id :
  ∀ {S : Scheme.{u}} {U : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsNoetherianAffine U],
    KernelKilledByPowIdealOfDefinition (𝟙 U))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.KernelKilledByPowIdealOfDefinition.ofHom :
  ∀ {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (g : U ⟶ V) {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B)
    (hφ : Function.Surjective φ)
    (hker : TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition (RingHom.ker φ))
    (hg : IsInducedBy g φ),
    KernelKilledByPowIdealOfDefinition g)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.KernelKilledByPowIdealOfDefinition.spec :
  ∀ {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (g : U ⟶ V) [KernelKilledByPowIdealOfDefinition g],
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
      (_ : TopologicalSpace A) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
      (φ : A →+* B),
        Function.Surjective φ ∧
          TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition (RingHom.ker φ) ∧
            IsInducedBy g φ)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.KernelKilledByPowIdealOfDefinition.iff :
  ∀ {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (g : U ⟶ V),
    KernelKilledByPowIdealOfDefinition g ↔
      ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B)
        (_ : TopologicalSpace A) (_ : TopologicalSpace B)
        (_ : TopologicalRing.IsAdicRing A) (_ : TopologicalRing.IsAdicRing B)
        (_ : IsNoetherianRing A) (_ : IsNoetherianRing B)
        (φ : A →+* B),
          Function.Surjective φ ∧
            TopologicalRing.Ideal.IsKilledByPowIdealOfDefinition (RingHom.ker φ) ∧
              IsInducedBy g φ)
