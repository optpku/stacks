module

public import Mathlib.Algebra.Module.TransferInstance
public import stacks_project.Chap98.«98_8_0_1_TangentSpace»
public import stacks_project.Chap98.«98_8_0_2_InfinitesimalAut»
public import stacks_project.Chap98.Lemma_98_21_2_Functor

public import ReasLib.AlgebraicGeometry.GroupoidsOver.PredeformationComparison

/-!
# Comparison of predeformation and geometric tangent spaces

The chapter import surface retains the tangent-space and infinitesimal-automorphism
foundations together with the two linear comparisons.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidsOver.Predeformation

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))

/-- The tangent space of residue lifts has the canonical dual-number additive group structure. -/
instance tangentSpace.instAddCommGroup [HasStrongRimSchlessinger X] :
    AddCommGroup (tangentSpace openImmersion kToS h_factor X x0) :=
  instAddCommGroup_tangentSpace openImmersion kToS h_factor X x0

/-- The tangent space of residue lifts has the canonical dual-number module structure. -/
instance tangentSpace.instModule [HasStrongRimSchlessinger X] :
    Module k (tangentSpace openImmersion kToS h_factor X x0) :=
  instModule_tangentSpace openImmersion kToS h_factor X x0

end AlgebraicGeometry.GroupoidsOver.Predeformation

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.tangentSpaceEquiv :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
      {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
      (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
      (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
      (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))
      [hRS : HasStrongRimSchlessinger X],
    CategoryTheory.Functor.tangentSpace
        (predeformationFunctor X openImmersion kToS h_factor x0) ≃ₗ[k]
      ((tangentFunctor x0).obj (ModuleCat.of k k) : Type (u + 1)))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.infinitesimalAutEquiv :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
      {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k]
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
      (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
      (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
      (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS))
      [hRS : HasStrongRimSchlessinger X],
    (infinitesimalAutomorphisms openImmersion kToS h_factor X x0
        (dualNumberPullback openImmersion kToS h_factor X x0)
        (dualNumberPullbackHom openImmersion kToS h_factor X x0) : Type u) ≃ₗ[k]
      ((infFunctor x0).obj (ModuleCat.of k k) : Type u))
