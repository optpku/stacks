module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Definition_90_19_2
public import stacks_project.Chap93.Example_93_4_1_Finite_projective_modules_Slice
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tangent space and infinitesimal automorphisms of `Def_V`

In Example 93.4.1, if `V` is a finite-dimensional `k`-vector space, then
`T Def_V = (0)` and `Inf(Def_V) = End_k(V)` are finite-dimensional.

`Functor.tangentSpace` from Definition 90.12.1 lives on a parallel
`IsPredeformationCategory`/`dualNumber` copy and cannot be imported together
with Example 93.4.1 or Definition 90.19.2. The tangent space below is the same
isomorphism-class construction, indexed by the dual-number object used by
`Inf_{x₀}(F)`.
-/

@[expose] public section

open CategoryTheory
open Functor.Fiber
open scoped DualNumber

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat.FiniteProjective

/-- The residue object of `C_Λ` has the same field structure as `k`. -/
instance instField_residueCarrier : Field (ArtinianLocalAlgCat.residue Λ k).carrier :=
  inferInstanceAs (Field k)

/-- A `k`-module is a module over the residue carrier. -/
instance instModule_residueCarrier (V : Type u) [AddCommGroup V] [Module k V] :
    Module (ArtinianLocalAlgCat.residue Λ k).carrier V :=
  inferInstanceAs (Module k V)

/-- Finite-dimensionality of `V` is preserved under the residue carrier identification. -/
instance instFiniteDimensional_residueCarrier (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    FiniteDimensional (ArtinianLocalAlgCat.residue Λ k).carrier V :=
  inferInstanceAs (FiniteDimensional k V)

/-- The finite projective residue-fibre module of `x₀ = (k, V)`. -/
abbrev moduleOf (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    ModuleCat.FiniteProjective.{u, u} (ArtinianLocalAlgCat.residue Λ k).carrier :=
  (fiberToCore (ArtinianLocalAlgCat.residue Λ k) (residueObject V)).of

/-- `moduleOf` recovers the finite projective module stored in `residueObject`. -/
theorem moduleOf_eq (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    moduleOf Λ k V = (fiberToCore (ArtinianLocalAlgCat.residue Λ k) (residueObject V)).of := sorry

/-- The trivial dual-number module `k[ε] ⊗_k V`. -/
abbrev trivialModule (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    ModuleCat.FiniteProjective.{u, u} (ArtinianLocalAlgCat.dualNumber Λ k).carrier :=
  (extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k)).obj (moduleOf Λ k V)

/-- Unfolding of `trivialModule`. -/
theorem trivialModule_eq (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    trivialModule Λ k V =
      (extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k)).obj (moduleOf Λ k V) := sorry

/-- The trivial dual-number deformation of `x₀ = (k, V)`, obtained by extension of scalars
along `residueToDualNumber`. -/
def trivialDeformation (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (groupoids Λ k).p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k) :=
  ⟨mkObj (ArtinianLocalAlgCat.dualNumber Λ k) (trivialModule Λ k V), rfl⟩

/-- The underlying object of `trivialDeformation` is the Grothendieck pair
`(k[ε], k[ε] ⊗_k V)`. -/
theorem trivialDeformation_obj (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    fiberInclusion.obj (trivialDeformation Λ k V) =
      mkObj (ArtinianLocalAlgCat.dualNumber Λ k) (trivialModule Λ k V) := sorry

/-- The canonical strongly cocartesian pushforward of `x₀` along `k ⟶ k[ε]`. -/
def trivialPushforward (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    fiberInclusion.obj
        (residueObject V : (groupoids Λ k).p.Fiber (ArtinianLocalAlgCat.residue Λ k)) ⟶
      fiberInclusion.obj (trivialDeformation Λ k V) :=
  mkHom (ArtinianLocalAlgCat.residueToDualNumber Λ k) (Iso.refl _)

/-- The base map of `trivialPushforward` is `residueToDualNumber`. -/
theorem trivialPushforward_base (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    (groupoids Λ k).p.map (trivialPushforward Λ k V) =
      ArtinianLocalAlgCat.residueToDualNumber Λ k := sorry

/-- The canonical pushforward of `x₀` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    (groupoids Λ k).p.IsStronglyCocartesian
      (ArtinianLocalAlgCat.residueToDualNumber Λ k) (trivialPushforward Λ k V) := sorry

/-- The comparison isomorphism `(k[ε] ⊗_k V) ⊗_{k[ε]} k ≅ V` used to retract the trivial
deformation. -/
def trivialRetractIso (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (extendScalars (ArtinianLocalAlgCat.dualNumberToResidue Λ k)).obj (trivialModule Λ k V) ≅
      moduleOf Λ k V :=
  let e :=
    ((ModuleCat.extendScalarsComp
          (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom
          (ArtinianLocalAlgCat.dualNumberToResidue Λ k).hom.toRingHom).app
        (moduleOf Λ k V).obj).symm ≪≫
      eqToIso
        (congrArg (fun h ↦ (ModuleCat.extendScalars h).obj (moduleOf Λ k V).obj)
          (RingHom.ext fun _ ↦ rfl)) ≪≫
      (ModuleCat.extendScalarsId (ArtinianLocalAlgCat.residue Λ k).carrier).app
        (moduleOf Λ k V).obj
  { hom := ObjectProperty.homMk e.hom
    inv := ObjectProperty.homMk e.inv
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The underlying module map of `trivialRetractIso` is the composite of
`ModuleCat.extendScalarsComp` with `ModuleCat.extendScalarsId`. -/
theorem trivialRetractIso_hom (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] :
    (trivialRetractIso Λ k V).hom.hom =
      ((ModuleCat.extendScalarsComp
            (ArtinianLocalAlgCat.residueToDualNumber Λ k).hom.toRingHom
            (ArtinianLocalAlgCat.dualNumberToResidue Λ k).hom.toRingHom).app
          (moduleOf Λ k V).obj).symm.hom ≫
        (eqToIso
            (congrArg (fun h ↦ (ModuleCat.extendScalars h).obj (moduleOf Λ k V).obj)
              (RingHom.ext fun _ ↦ rfl))).hom ≫
          ((ModuleCat.extendScalarsId
              (ArtinianLocalAlgCat.residue Λ k).carrier).app (moduleOf Λ k V).obj).hom := sorry

/-- The unique dual-number lift of `V` in the slice `Def_V`, given by the pair
`(k[ε] ⊗_k V, α)` with `α` the canonical retraction over `k[ε] ⟶ k`. -/
def trivialLift (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    (deformation V).p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k) :=
  ⟨Over.mk (mkHom (ArtinianLocalAlgCat.dualNumberToResidue Λ k) (trivialRetractIso Λ k V)), rfl⟩

/-- `trivialLift` is the over-object associated to the canonical retraction of the trivial
deformation. -/
theorem trivialLift_mk (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    fiberInclusion.obj (trivialLift Λ k V) =
      Over.mk (mkHom (ArtinianLocalAlgCat.dualNumberToResidue Λ k) (trivialRetractIso Λ k V)) :=
  sorry

/-- The tangent space `T Def_V` is the type of isomorphism classes of objects in the fibre of
`Def_V` over `k[ε]`. -/
def tangentSpace (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    Type (u + 1) :=
  isomorphismClasses.obj (Cat.of ((deformation V).p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k)))

/-- Unfolding of `tangentSpace`. -/
theorem tangentSpace_def (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    tangentSpace Λ k V =
      isomorphismClasses.obj
        (Cat.of ((deformation V).p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k))) := sorry

/-- The isomorphism class of a dual-number lift of `V`. -/
def tangentSpace.mk (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (x : (deformation V).p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    tangentSpace Λ k V :=
  Quotient.mk'' x

/-- `tangentSpace.mk` is the class of the given dual-number fibre object. -/
theorem tangentSpace.mk_eq (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (x : (deformation V).p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    tangentSpace.mk Λ k V x = Quotient.mk'' x := sorry

/-- The zero tangent vector of `Def_V`, as the isomorphism class of the unique dual-number
lift of `V`. -/
def trivialTangent (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    tangentSpace Λ k V :=
  tangentSpace.mk Λ k V (trivialLift Λ k V)

/-- `trivialTangent` is the class of `trivialLift`. -/
theorem trivialTangent_spec (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    trivialTangent Λ k V = tangentSpace.mk Λ k V (trivialLift Λ k V) := sorry

/-- Lemma 93.4.3 (1): the tangent space `T Def_V` consists of a single isomorphism class. -/
@[stacks 0DVQ]
theorem eq_trivialTangent (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (x : tangentSpace Λ k V) : x = trivialTangent Λ k V := sorry

/-- The infinitesimal generator `ε` as an element of the dual-number carrier. -/
def epsCarrier : (ArtinianLocalAlgCat.dualNumber Λ k).carrier := DualNumber.eps

/-- `epsCarrier` is the dual-number generator `ε`. -/
theorem epsCarrier_eq : epsCarrier Λ k = DualNumber.eps := sorry

/-- Extension of scalars of an endomorphism `ψ : End_k(V)` to the trivial dual-number
deformation. -/
def extendEnd (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) : trivialModule Λ k V ⟶ trivialModule Λ k V :=
  (extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k)).map
    (ObjectProperty.homMk (ModuleCat.ofHom ψ))

/-- Unfolding of `extendEnd`. -/
theorem extendEnd_eq (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    extendEnd Λ k V ψ =
      (extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k)).map
        (ObjectProperty.homMk (ModuleCat.ofHom ψ)) := sorry

/-- The endomorphism `id + ε • ψ` of the trivial dual-number deformation, for
`ψ : End_k(V)`. -/
def idAddEps (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) : (trivialModule Λ k V).obj ⟶ (trivialModule Λ k V).obj :=
  𝟙 (trivialModule Λ k V).obj + epsCarrier Λ k • (extendEnd Λ k V ψ).hom

/-- `idAddEps ψ` is the `k[ε]`-linear map `id + ε • extendScalars.map ψ`. -/
theorem idAddEps_def (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    idAddEps Λ k V ψ =
      𝟙 (trivialModule Λ k V).obj + epsCarrier Λ k • (extendEnd Λ k V ψ).hom := sorry

/-- The finite-projective automorphism of the trivial deformation induced by `id + ε ψ`. -/
def idAddEpsIso (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) : trivialModule Λ k V ≅ trivialModule Λ k V :=
  { hom := ObjectProperty.homMk (idAddEps Λ k V ψ)
    inv := ObjectProperty.homMk (idAddEps Λ k V (-ψ))
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The underlying forward map of `idAddEpsIso` is `idAddEps`. -/
theorem idAddEpsIso_hom (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    (idAddEpsIso Λ k V ψ).hom.hom = idAddEps Λ k V ψ := sorry

/-- The fibre automorphism of the trivial dual-number deformation associated to
`ψ : End_k(V)`. -/
def infAutOfEnd (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    Functor.infinitesimalAutomorphismsAt (groupoids Λ k).p (residueObject V)
      (trivialDeformation Λ k V) (trivialPushforward Λ k V) :=
  ⟨isoMk
      { hom :=
          mkHom (𝟙 (ArtinianLocalAlgCat.dualNumber Λ k))
            ((extendScalarsId (ArtinianLocalAlgCat.dualNumber Λ k)).app (trivialModule Λ k V) ≪≫
              idAddEpsIso Λ k V ψ)
        inv :=
          mkHom (𝟙 (ArtinianLocalAlgCat.dualNumber Λ k))
            ((extendScalarsId (ArtinianLocalAlgCat.dualNumber Λ k)).app (trivialModule Λ k V) ≪≫
              (idAddEpsIso Λ k V ψ).symm)
        hom_inv_id := sorry
        inv_hom_id := sorry }
      sorry,
    sorry⟩

/-- Elements of the image of `infAutOfEnd` are represented by `id + ε ψ`. -/
theorem infAutOfEnd_spec (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    fiberInclusion.map (infAutOfEnd Λ k V ψ).val.hom =
      mkHom (𝟙 (ArtinianLocalAlgCat.dualNumber Λ k))
        ((extendScalarsId (ArtinianLocalAlgCat.dualNumber Λ k)).app (trivialModule Λ k V) ≪≫
          idAddEpsIso Λ k V ψ) := sorry

/-- Membership of `infAutOfEnd ψ` in `Inf_{x₀}(F)`. -/
theorem mem_infAutOfEnd (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    (infAutOfEnd Λ k V ψ).val ∈
      Functor.infinitesimalAutomorphismsAt (groupoids Λ k).p (residueObject V)
        (trivialDeformation Λ k V) (trivialPushforward Λ k V) := sorry

/-- The identification `End_k(V) → Inf_{x₀}(F)` sends addition to composition of
automorphisms. -/
theorem infAutOfEnd_map_add (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ φ : Module.End k V) :
    infAutOfEnd Λ k V (ψ + φ) = infAutOfEnd Λ k V ψ * infAutOfEnd Λ k V φ := sorry

/-- Lemma 93.4.3 (2): infinitesimal automorphisms of `Def_V` are identified with `End_k(V)`. -/
@[stacks 0DVQ]
theorem infAutOfEnd_bijective (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] : Function.Bijective (infAutOfEnd Λ k V) := sorry

/-- Lemma 93.4.3 (3): `End_k(V)` is finite-dimensional, hence so is `Inf(Def_V)`. -/
@[stacks 0DVQ]
theorem finiteDimensional_end (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] : FiniteDimensional k (Module.End k V) := sorry

end ArtinianLocalAlgCat.FiniteProjective
