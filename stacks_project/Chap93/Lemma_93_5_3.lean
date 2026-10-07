module

public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Abelian.Extension.Basic
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import stacks_project.Chap93.Lemma_93_5_3_Deformation

/-!
# Tangent space and infinitesimal automorphisms of `Def_{V, ρ0}`

In Example 93.5.1, `T Def_{V, ρ0}` identifies with `Ext^1_{k[Γ]}(V, V)` and with
`H^1(Γ, End_k(V))`, while `Inf(Def_{V, ρ0})` identifies with `H^0(Γ, End_k(V))`.
-/

@[expose] public section

open CategoryTheory Functor
open scoped DualNumber

noncomputable section

universe u

namespace GroupRepCat

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]
variable {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The residue representation `ρ0`, as a `k`-linear representation of `Γ` on `V`. -/
def residueRepresentation (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Representation k Γ V :=
  toRepresentation (ofResidue Γ Λ k ρ0)

/-- Unfolding of `residueRepresentation`. -/
theorem residueRepresentation_eq (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    residueRepresentation Γ Λ k ρ0 = toRepresentation (ofResidue Γ Λ k ρ0) := sorry

/-- The conjugation representation of `Γ` on `End_k(V)`. -/
def endRepresentation (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Representation k Γ (Module.End k V) :=
  Representation.linHom (residueRepresentation Γ Λ k ρ0) (residueRepresentation Γ Λ k ρ0)

/-- The action of `γ` on `End_k(V)` is conjugation by `ρ0 γ`. -/
theorem endRepresentation_apply (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (γ : Γ) (ψ : Module.End k V) :
    endRepresentation Γ Λ k ρ0 γ ψ =
      residueRepresentation Γ Λ k ρ0 γ ∘ₗ ψ ∘ₗ
        residueRepresentation Γ Λ k ρ0 γ⁻¹ := sorry

/-- Membership in `H^0(Γ, End_k(V))` is commutation with the action `ρ0`. -/
theorem mem_endRepresentation_invariants_iff (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (ψ : Module.End k V) :
    ψ ∈ (endRepresentation Γ Λ k ρ0).invariants ↔
      ∀ γ : Γ, ψ ∘ₗ (ρ0 γ).val = (ρ0 γ).val ∘ₗ ψ := sorry

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
def idAddEpsIso (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (ψ : Module.End k V) :
    trivialDeformationObj Γ Λ k ρ0 ≅ trivialDeformationObj Γ Λ k ρ0 where
  hom := Hom.of (𝟙 (trivialDeformationObj Γ Λ k ρ0).base) (fun m ↦ idAddEps Λ k ψ m)
    sorry sorry sorry sorry
  inv := Hom.of (𝟙 (trivialDeformationObj Γ Λ k ρ0).base) (fun m ↦ idAddEps Λ k (-ψ) m)
    sorry sorry sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying forward map of `idAddEpsIso` is `idAddEps`. -/
theorem idAddEpsIso_hom (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (ψ : Module.End k V) :
    (idAddEpsIso Γ Λ k ρ0 ψ).hom.toFun = fun m ↦ idAddEps Λ k ψ m := sorry

/-- The map `H^0(Γ, End_k(V)) → Inf_{x0}(F)` sending `ψ` to the infinitesimal automorphism
`id + ε ψ`. -/
def infAutOfInvariants (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (ψ : (endRepresentation Γ Λ k ρ0).invariants) :
    Functor.infinitesimalAutomorphismsAt (forget Γ Λ k) (residueObj Γ Λ k ρ0)
      (trivialDeformation Γ Λ k ρ0) (trivialPushforward Γ Λ k ρ0) :=
  ⟨Fiber.isoMk (idAddEpsIso Γ Λ k ρ0 ψ.val) sorry, sorry⟩

/-- Elements of the image of `infAutOfInvariants` are represented by `id + ε ψ`. -/
theorem infAutOfInvariants_spec (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (ψ : (endRepresentation Γ Λ k ρ0).invariants) :
    (Fiber.fiberInclusion.map (infAutOfInvariants Γ Λ k ρ0 ψ).val.hom).toFun =
      fun m ↦ idAddEps Λ k ψ.val m := sorry

/-- The identification `H^0(Γ, End_k(V)) → Inf_{x0}(F)` sends addition to composition of
automorphisms. -/
theorem infAutOfInvariants_map_add (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (ψ φ : (endRepresentation Γ Λ k ρ0).invariants) :
    infAutOfInvariants Γ Λ k ρ0 (ψ + φ) =
      infAutOfInvariants Γ Λ k ρ0 ψ * infAutOfInvariants Γ Λ k ρ0 φ := sorry

/-- Lemma 93.5.3 (1)
In Example 93.5.1, `Inf(Def_{V, ρ0})` identifies with `H^0(Γ, End_k(V))` via
`ψ ↦ id + ε ψ`. -/
@[stacks 0DVT]
theorem infAutOfInvariants_bijective (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Function.Bijective (infAutOfInvariants Γ Λ k ρ0) := sorry

/-- The tangent space `T Def_{V, ρ0}` as isomorphism classes of dual-number fibre objects of
`deformationForget ρ0`. -/
def tangentSpace (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) : Type (u + 1) :=
  isomorphismClasses.obj (Cat.of ((deformationForget Γ Λ k ρ0).Fiber
    (ArtinianLocalAlgCat.dualNumber Λ k)))

/-- Unfolding of `tangentSpace`. -/
theorem tangentSpace_def (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    tangentSpace Γ Λ k ρ0 =
      isomorphismClasses.obj (Cat.of ((deformationForget Γ Λ k ρ0).Fiber
        (ArtinianLocalAlgCat.dualNumber Λ k))) := sorry

/-- The isomorphism class of a dual-number lift of `(V, ρ0)`. -/
def tangentSpace.mk (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (x : (deformationForget Γ Λ k ρ0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    tangentSpace Γ Λ k ρ0 :=
  Quotient.mk'' x

/-- `tangentSpace.mk` is the class of the given dual-number fibre object. -/
theorem tangentSpace.mk_eq (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (x : (deformationForget Γ Λ k ρ0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    tangentSpace.mk Γ Λ k ρ0 x = Quotient.mk'' x := sorry

/-- The `k[ε]`-module structure on the middle term of an extension `0 → V → E → V → 0`,
with `ε` acting through the composition `E → V → E`. -/
instance ofExtensionModule (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (S : Extension (Rep.of (residueRepresentation Γ Λ k ρ0))
      (Rep.of (residueRepresentation Γ Λ k ρ0))) :
    Module (ArtinianLocalAlgCat.dualNumber Λ k).carrier S.E.V where
  smul x m :=
    (x.fst : k) • (m : S.E.V) + x.snd • S.f.hom (S.g.hom (m : S.E.V))
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry


/-- The dual-number `GroupRepCat` object associated to an extension of `Γ`-modules
`0 → V → E → V → 0`. -/
def ofExtensionObj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (S : Extension (Rep.of (residueRepresentation Γ Λ k ρ0))
      (Rep.of (residueRepresentation Γ Λ k ρ0))) :
    GroupRepCat Γ Λ k where
  base := ArtinianLocalAlgCat.dualNumber Λ k
  module := S.E.V
  addCommGroup := inferInstance
  isModule := ofExtensionModule Γ Λ k ρ0 S
  finiteProjective := sorry
  rho :=
    { toFun γ :=
        LinearMap.GeneralLinearGroup.ofLinearEquiv
          (LinearEquiv.ofLinear
            { toFun := fun m ↦ S.E.ρ γ m, map_add' := sorry, map_smul' := sorry }
            { toFun := fun m ↦ S.E.ρ γ⁻¹ m, map_add' := sorry, map_smul' := sorry }
            sorry sorry)
      map_one' := sorry
      map_mul' := sorry }

/-- On `ofExtensionObj S`, a dual number `a + b ε` acts by `a • m + b • (f (g m))`. -/
theorem ofExtensionObj_smul (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (S : Extension (Rep.of (residueRepresentation Γ Λ k ρ0))
      (Rep.of (residueRepresentation Γ Λ k ρ0)))
    (x : (ArtinianLocalAlgCat.dualNumber Λ k).carrier) (m : S.E.V) :
    x • m = x.fst • m + x.snd • S.f.hom (S.g.hom m) := sorry

/-- The base of `ofExtensionObj` is `k[ε]`. -/
theorem ofExtensionObj_base (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (S : Extension (Rep.of (residueRepresentation Γ Λ k ρ0))
      (Rep.of (residueRepresentation Γ Λ k ρ0))) :
    (ofExtensionObj Γ Λ k ρ0 S).base = ArtinianLocalAlgCat.dualNumber Λ k := sorry

/-- The reduction map `E → V` as a morphism of triples over `k[ε] ⟶ k`. -/
def ofExtensionHom (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (S : Extension (Rep.of (residueRepresentation Γ Λ k ρ0))
      (Rep.of (residueRepresentation Γ Λ k ρ0))) :
    ofExtensionObj Γ Λ k ρ0 S ⟶ ofResidue Γ Λ k ρ0 :=
  Hom.of (ArtinianLocalAlgCat.dualNumberToResidue Λ k) (fun m ↦ S.g.hom m)
    sorry sorry sorry sorry

/-- The underlying function of `ofExtensionHom` is the extension's projection `E → V`. -/
theorem ofExtensionHom_toFun (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (S : Extension (Rep.of (residueRepresentation Γ Λ k ρ0))
      (Rep.of (residueRepresentation Γ Λ k ρ0))) :
    (ofExtensionHom Γ Λ k ρ0 S).toFun = fun m ↦ S.g.hom m := sorry

/-- The dual-number fibre object of `Def_{V, ρ0}` associated to an extension of `V` by `V`. -/
def ofExtensionFiber (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (S : Extension (Rep.of (residueRepresentation Γ Λ k ρ0))
      (Rep.of (residueRepresentation Γ Λ k ρ0))) :
    (deformationForget Γ Λ k ρ0).Fiber (ArtinianLocalAlgCat.dualNumber Λ k) :=
  ⟨Over.mk (ofExtensionHom Γ Λ k ρ0 S), sorry⟩

/-- The underlying Over-object of `ofExtensionFiber` is `Over.mk (ofExtensionHom S)`. -/
theorem ofExtensionFiber_obj (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (S : Extension (Rep.of (residueRepresentation Γ Λ k ρ0))
      (Rep.of (residueRepresentation Γ Λ k ρ0))) :
    Fiber.fiberInclusion.obj (ofExtensionFiber Γ Λ k ρ0 S) =
      Over.mk (ofExtensionHom Γ Λ k ρ0 S) := sorry

/-- The comparison map sending an extension of `Γ`-modules `0 → V → E → V → 0` to the
corresponding class in `T Def_{V, ρ0}`. -/
def ofExtension (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (S : Extension (Rep.of (residueRepresentation Γ Λ k ρ0))
      (Rep.of (residueRepresentation Γ Λ k ρ0))) :
    tangentSpace Γ Λ k ρ0 :=
  tangentSpace.mk Γ Λ k ρ0 (ofExtensionFiber Γ Λ k ρ0 S)

/-- `ofExtension S` is the isomorphism class of the dual-number fibre object attached to `S`. -/
theorem ofExtension_spec (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (S : Extension (Rep.of (residueRepresentation Γ Λ k ρ0))
      (Rep.of (residueRepresentation Γ Λ k ρ0))) :
    ofExtension Γ Λ k ρ0 S = tangentSpace.mk Γ Λ k ρ0 (ofExtensionFiber Γ Λ k ρ0 S) := sorry

/-- Iso-classes of extensions are identified by `ofExtension`. -/
theorem ofExtension_iso_iff (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (S T : Extension (Rep.of (residueRepresentation Γ Λ k ρ0))
      (Rep.of (residueRepresentation Γ Λ k ρ0))) :
    ofExtension Γ Λ k ρ0 S = ofExtension Γ Λ k ρ0 T ↔ Nonempty (S ≅ T) := sorry

/-- Lemma 93.5.3 (2)
In Example 93.5.1, `T Def_{V, ρ0}` identifies with `Ext^1_{k[Γ]}(V, V)` via the comparison
that lets `ε` act through an extension `0 → V → E → V → 0`. -/
@[stacks 0DVT]
theorem ofExtension_surjective (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Function.Surjective (ofExtension Γ Λ k ρ0) := sorry

/-- Lemma 93.5.3 (3)
`Ext^1_{k[Γ]}(V, V)` identifies with `H^1(Γ, End_k(V))`. -/
@[stacks 0DVT]
theorem nonempty_extIsoH1 (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    Nonempty
      (((Ext k (Rep k Γ) 1).obj
          (Opposite.op (Rep.of (residueRepresentation Γ Λ k ρ0)))).obj
        (Rep.of (residueRepresentation Γ Λ k ρ0)) ≅
        groupCohomology.H1 (Rep.of (endRepresentation Γ Λ k ρ0))) := sorry

/-- Lemma 93.5.3 (4)
`Inf(Def_{V, ρ0})` is always finite-dimensional, as a subspace of `End_k(V)`. -/
@[stacks 0DVT]
theorem finiteDimensional_invariants (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    FiniteDimensional k (endRepresentation Γ Λ k ρ0).invariants := sorry

/-- Lemma 93.5.3 (5)
If `Γ` is finitely generated, then `T Def_{V, ρ0}` is finite-dimensional, as
`H^1(Γ, End_k(V))` is finite-dimensional. -/
@[stacks 0DVT]
theorem finiteDimensional_h1 (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) [Group.FG Γ] :
    FiniteDimensional k (groupCohomology.H1 (Rep.of (endRepresentation Γ Λ k ρ0))) := sorry

end GroupRepCat
