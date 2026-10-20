module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import stacks_project.Chap88.Definition_88_20_1_LocallyNoetherian
public import stacks_project.Chap88.Definition_88_20_1_Ring

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineRigEtale

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineMorphism

/-!
# Affine formal algebraic spaces induced by adic Noetherian homomorphisms

A morphism of affine formal algebraic spaces corresponds to a continuous
homomorphism `φ : A →+* B` of adic Noetherian topological rings when the
source (resp. target) is a directed affine thickening of successive quotient
spectra of `B` (resp. `A`), and the morphism is the contravariant colimit of
`Spec` of the finite-level quotient maps of `φ`. The correspondence is
contravariant: `φ : A →+* B` induces a map from the thickening of `B` to the
thickening of `A`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsInducedBy :
  ∀ {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u} (g : U ⟶ V)
    {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B], (A →+* B) → Prop)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.RigEtale :
  ∀ {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U] [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V] [FormalAlgebraicSpace.IsAffine V],
    (U ⟶ V) → Prop)
