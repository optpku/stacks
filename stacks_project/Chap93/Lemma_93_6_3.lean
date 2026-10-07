module

public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Cohomology
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.Topology.Algebra.Group.FiniteGeneration
public import stacks_project.Chap93.Lemma_93_6_3_Deformation

/-!
# Tangent space and infinitesimal automorphisms of `Def_{V, ρ0}`

In Example 93.6.1, `T Def_{V, ρ0}` identifies with `H^1(Γ, End_k(V))`, while
`Inf(Def_{V, ρ0})` identifies with `H^0(Γ, End_k(V))`.
-/

@[expose] public section

open CategoryTheory Functor
open CategoryTheory.Action.ModuleCat
open CategoryTheory.Action.ModuleCat.DiscreteModuleCat
open scoped DualNumber

noncomputable section

universe u

namespace ContinuousRep

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The residue representation `ρ0`, as a `k`-linear representation of `Γ` on `V`. -/
def residueRepresentation (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    Representation k Γ V :=
  toRepresentation (ofResidue Γ Λ k ρ0 hρ0)

/-- Unfolding of `residueRepresentation`. -/
theorem residueRepresentation_eq (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    residueRepresentation Γ Λ k ρ0 hρ0 = toRepresentation (ofResidue Γ Λ k ρ0 hρ0) := sorry

/-- The conjugation representation of `Γ` on `End_k(V)`. -/
def endRepresentation (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    Representation k Γ (Module.End k V) :=
  Representation.linHom (residueRepresentation Γ Λ k ρ0 hρ0)
    (residueRepresentation Γ Λ k ρ0 hρ0)

/-- The action of `γ` on `End_k(V)` is conjugation by `ρ0 γ`. -/
theorem endRepresentation_apply (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) (γ : Γ) (ψ : Module.End k V) :
    endRepresentation Γ Λ k ρ0 hρ0 γ ψ =
      residueRepresentation Γ Λ k ρ0 hρ0 γ ∘ₗ ψ ∘ₗ
        residueRepresentation Γ Λ k ρ0 hρ0 γ⁻¹ := sorry

/-- Membership in `H^0(Γ, End_k(V))` is commutation with the action `ρ0`. -/
theorem mem_endRepresentation_invariants_iff
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0)
    (ψ : Module.End k V) :
    ψ ∈ (endRepresentation Γ Λ k ρ0 hρ0).invariants ↔
      ∀ γ : Γ, ψ ∘ₗ (ρ0 γ).val = (ρ0 γ).val ∘ₗ ψ := sorry

/-- `End_k(V)` as a discrete continuous `Γ`-module, via the conjugation action. -/
def endDiscreteModule (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    DiscreteModuleCat k Γ where
  obj := (Rep.RepToAction k Γ).obj (Rep.of (endRepresentation Γ Λ k ρ0 hρ0))
  property := sorry

/-- The underlying action of `endDiscreteModule` is `RepToAction` of the conjugation
representation. -/
theorem endDiscreteModule_obj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    (endDiscreteModule Γ Λ k ρ0 hρ0).obj =
      (Rep.RepToAction k Γ).obj (Rep.of (endRepresentation Γ Λ k ρ0 hρ0)) := sorry

/-- The infinitesimal generator `ε` as an element of the dual-number carrier. -/
def epsCarrier : (ArtinianLocalAlgCat.dualNumber Λ k).carrier := DualNumber.eps

/-- `epsCarrier` is the dual-number generator `ε`. -/
theorem epsCarrier_eq : epsCarrier Λ k = DualNumber.eps := sorry

/-- The endomorphism `id + ε • ψ` of the trivial dual-number deformation. -/
def idAddEps (ψ : Module.End k V) :
    Module.End (ArtinianLocalAlgCat.dualNumber Λ k).carrier (trivialModule Λ k V) :=
  LinearMap.id + epsCarrier Λ k • extendEnd Λ k V ψ

/-- `idAddEps ψ` is the `k[ε]`-linear map `id + ε • extendEnd ψ`. -/
theorem idAddEps_def (ψ : Module.End k V) :
    idAddEps Λ k ψ = LinearMap.id + epsCarrier Λ k • extendEnd Λ k V ψ := sorry

/-- The automorphism of the trivial dual-number object induced by `id + ε ψ`. -/
def idAddEpsIso (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) (ψ : Module.End k V) :
    trivialDeformationObj Γ Λ k ρ0 hρ0 ≅ trivialDeformationObj Γ Λ k ρ0 hρ0 where
  hom := Hom.of (𝟙 (trivialDeformationObj Γ Λ k ρ0 hρ0).base) (fun m ↦ idAddEps Λ k ψ m)
    sorry sorry sorry sorry
  inv := Hom.of (𝟙 (trivialDeformationObj Γ Λ k ρ0 hρ0).base) (fun m ↦ idAddEps Λ k (-ψ) m)
    sorry sorry sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying forward map of `idAddEpsIso` is `idAddEps`. -/
theorem idAddEpsIso_hom (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) (ψ : Module.End k V) :
    (idAddEpsIso Γ Λ k ρ0 hρ0 ψ).hom.toFun = fun m ↦ idAddEps Λ k ψ m := sorry

/-- The map `H^0(Γ, End_k(V)) → Inf_{x0}(F)` sending `ψ` to the infinitesimal automorphism
`id + ε ψ`. -/
def infAutOfInvariants (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) (ψ : (endRepresentation Γ Λ k ρ0 hρ0).invariants) :
    Functor.infinitesimalAutomorphismsAt (forget Γ Λ k) (residueObj Γ Λ k ρ0 hρ0)
      (trivialDeformation Γ Λ k ρ0 hρ0) (trivialPushforward Γ Λ k ρ0 hρ0) :=
  ⟨Fiber.isoMk (idAddEpsIso Γ Λ k ρ0 hρ0 ψ.val) sorry, sorry⟩

/-- Elements of the image of `infAutOfInvariants` are represented by `id + ε ψ`. -/
theorem infAutOfInvariants_spec (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) (ψ : (endRepresentation Γ Λ k ρ0 hρ0).invariants) :
    (Fiber.fiberInclusion.map (infAutOfInvariants Γ Λ k ρ0 hρ0 ψ).val.hom).toFun =
      fun m ↦ idAddEps Λ k ψ.val m := sorry

/-- The identification `H^0(Γ, End_k(V)) → Inf_{x0}(F)` sends addition to composition of
automorphisms. -/
theorem infAutOfInvariants_map_add (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0)
    (ψ φ : (endRepresentation Γ Λ k ρ0 hρ0).invariants) :
    infAutOfInvariants Γ Λ k ρ0 hρ0 (ψ + φ) =
      infAutOfInvariants Γ Λ k ρ0 hρ0 ψ * infAutOfInvariants Γ Λ k ρ0 hρ0 φ := sorry

/-- The tangent space `T Def_{V, ρ0}` as isomorphism classes of dual-number fibre objects of
`deformationForget ρ0`. -/
def tangentSpace (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) : Type (u + 1) :=
  isomorphismClasses.obj (Cat.of ((deformationForget Γ Λ k ρ0 hρ0).Fiber
    (ArtinianLocalAlgCat.dualNumber Λ k)))

/-- Unfolding of `tangentSpace`. -/
theorem tangentSpace_def (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    tangentSpace Γ Λ k ρ0 hρ0 =
      isomorphismClasses.obj (Cat.of ((deformationForget Γ Λ k ρ0 hρ0).Fiber
        (ArtinianLocalAlgCat.dualNumber Λ k))) := sorry

/-- The isomorphism class of a dual-number lift of `(V, ρ0)`. -/
def tangentSpace.mk (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0)
    (x : (deformationForget Γ Λ k ρ0 hρ0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    tangentSpace Γ Λ k ρ0 hρ0 :=
  Quotient.mk'' x

/-- `tangentSpace.mk` is the class of the given dual-number fibre object. -/
theorem tangentSpace.mk_eq (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0)
    (x : (deformationForget Γ Λ k ρ0 hρ0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    tangentSpace.mk Γ Λ k ρ0 hρ0 x = Quotient.mk'' x := sorry

/-- Lemma 93.6.3 (1)
In Example 93.6.1, `T Def_{V, ρ0}` identifies with `H^1(Γ, End_k(V))`. -/
@[stacks 0DVW]
theorem nonempty_tangentEquivH1 (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    Nonempty
      (tangentSpace Γ Λ k ρ0 hρ0 ≃
        cohomologyObject k Γ 1 (endDiscreteModule Γ Λ k ρ0 hρ0)) := sorry

/-- Lemma 93.6.3 (2)
In Example 93.6.1, `Inf(Def_{V, ρ0})` identifies with `H^0(Γ, End_k(V))` via
`ψ ↦ id + ε ψ`. -/
@[stacks 0DVW]
theorem infAutOfInvariants_bijective (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    Function.Bijective (infAutOfInvariants Γ Λ k ρ0 hρ0) := sorry

/-- Lemma 93.6.3 (3)
`Inf(Def_{V, ρ0})` is always finite-dimensional, as a subspace of `End_k(V)`. -/
@[stacks 0DVW]
theorem finiteDimensional_invariants (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    FiniteDimensional k (endRepresentation Γ Λ k ρ0 hρ0).invariants := sorry

/-- Lemma 93.6.3 (4)
If `Γ` is topologically finitely generated, then `T Def_{V, ρ0}` is finite-dimensional, as
`H^1(Γ, End_k(V))` is finite-dimensional. -/
@[stacks 0DVW]
theorem finiteDimensional_h1 (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) (hΓ : TopologicalGroup.IsFinitelyGenerated Γ) :
    FiniteDimensional k (cohomologyObject k Γ 1 (endDiscreteModule Γ Λ k ρ0 hρ0)) := sorry

end ContinuousRep
