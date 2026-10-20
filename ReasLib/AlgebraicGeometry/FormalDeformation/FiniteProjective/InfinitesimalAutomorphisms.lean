module

public import Mathlib.Algebra.Module.LinearMap.End
public import ReasLib.AlgebraicGeometry.FormalDeformation.FiniteProjective.TangentSpace

/-!
# Infinitesimal automorphisms of a finite-projective deformation

For a finite-dimensional vector space, endomorphisms give all infinitesimal
automorphisms of the canonical dual-number deformation.
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

set_option backward.privateInPublic true

/-- The infinitesimal generator `ε` as an element of the dual-number carrier. -/
private def epsCarrier : (ArtinianLocalAlgCat.dualNumber Λ k).carrier := DualNumber.eps

/-- `epsCarrier` is the dual-number generator `ε`. -/
theorem epsCarrier_eq : epsCarrier Λ k = DualNumber.eps := rfl

/-- Extension of scalars of an endomorphism `ψ : End_k(V)` to the trivial deformation. -/
def extendEnd (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) : trivialModule Λ k V ⟶ trivialModule Λ k V :=
  (extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k)).map
    (ObjectProperty.homMk (ModuleCat.ofHom ψ))

/-- Unfolding of `extendEnd`. -/
theorem extendEnd_eq (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    extendEnd Λ k V ψ =
      (extendScalars (ArtinianLocalAlgCat.residueToDualNumber Λ k)).map
        (ObjectProperty.homMk (ModuleCat.ofHom ψ)) := rfl

/-- The endomorphism `id + ε • ψ` of the trivial dual-number deformation. -/
def idAddEps (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) : (trivialModule Λ k V).obj ⟶ (trivialModule Λ k V).obj :=
  𝟙 (trivialModule Λ k V).obj + epsCarrier Λ k • (extendEnd Λ k V ψ).hom

/-- `idAddEps ψ` is the `k[ε]`-linear map `id + ε • extendScalars.map ψ`. -/
theorem idAddEps_def (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    idAddEps Λ k V ψ =
      𝟙 (trivialModule Λ k V).obj + epsCarrier Λ k • (extendEnd Λ k V ψ).hom := rfl

/-- The finite-projective automorphism induced by `id + ε ψ`. -/
def idAddEpsIso (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) : trivialModule Λ k V ≅ trivialModule Λ k V :=
  let hom : trivialModule Λ k V ⟶ trivialModule Λ k V :=
    ObjectProperty.homMk (idAddEps Λ k V ψ)
  let inv : trivialModule Λ k V ⟶ trivialModule Λ k V :=
    ObjectProperty.homMk (idAddEps Λ k V (-ψ))
  have inverse_laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ := sorry
  { hom := hom
    inv := inv
    hom_inv_id := inverse_laws.1
    inv_hom_id := inverse_laws.2 }

/-- The underlying forward map of `idAddEpsIso` is `idAddEps`. -/
theorem idAddEpsIso_hom (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    (idAddEpsIso Λ k V ψ).hom.hom = idAddEps Λ k V ψ := rfl

/-- The fibre automorphism of the trivial deformation associated to `ψ : End_k(V)`. -/
def infAutOfEnd (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    Functor.infinitesimalAutomorphismsAt (groupoids Λ k).p (residueObject V)
      (trivialDeformation Λ k V) (trivialPushforward Λ k V) :=
  let hom : fiberInclusion.obj (trivialDeformation Λ k V) ⟶
      fiberInclusion.obj (trivialDeformation Λ k V) :=
    mkHom (𝟙 (ArtinianLocalAlgCat.dualNumber Λ k))
      ((extendScalarsId (ArtinianLocalAlgCat.dualNumber Λ k)).app (trivialModule Λ k V) ≪≫
        idAddEpsIso Λ k V ψ)
  let inv : fiberInclusion.obj (trivialDeformation Λ k V) ⟶
      fiberInclusion.obj (trivialDeformation Λ k V) :=
    mkHom (𝟙 (ArtinianLocalAlgCat.dualNumber Λ k))
      ((extendScalarsId (ArtinianLocalAlgCat.dualNumber Λ k)).app (trivialModule Λ k V) ≪≫
        (idAddEpsIso Λ k V ψ).symm)
  have laws : hom ≫ inv = 𝟙 _ ∧ inv ≫ hom = 𝟙 _ ∧
      ∀ γ : Aut (trivialDeformation Λ k V), fiberInclusion.map γ.hom = hom →
        γ ∈ Functor.infinitesimalAutomorphismsAt (groupoids Λ k).p (residueObject V)
          (trivialDeformation Λ k V) (trivialPushforward Λ k V) := sorry
  let γ := isoMk
    { hom := hom
      inv := inv
      hom_inv_id := laws.1
      inv_hom_id := laws.2.1 }
    (CategoryTheory.IsHomLift.map (groupoids Λ k).p hom)
  ⟨γ, laws.2.2 γ rfl⟩

/-- Elements in the image of `infAutOfEnd` are represented by `id + ε ψ`. -/
theorem infAutOfEnd_spec (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    fiberInclusion.map (infAutOfEnd Λ k V ψ).val.hom =
      mkHom (𝟙 (ArtinianLocalAlgCat.dualNumber Λ k))
        ((extendScalarsId (ArtinianLocalAlgCat.dualNumber Λ k)).app (trivialModule Λ k V) ≪≫
          idAddEpsIso Λ k V ψ) := rfl

/-- Membership of `infAutOfEnd ψ` in the infinitesimal-automorphism subgroup. -/
theorem mem_infAutOfEnd (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ : Module.End k V) :
    (infAutOfEnd Λ k V ψ).val ∈
      Functor.infinitesimalAutomorphismsAt (groupoids Λ k).p (residueObject V)
        (trivialDeformation Λ k V) (trivialPushforward Λ k V) := (infAutOfEnd Λ k V ψ).property

/-- The identification `End_k(V) → Inf_{x₀}(F)` sends addition to composition. -/
theorem infAutOfEnd_map_add (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ψ φ : Module.End k V) :
    infAutOfEnd Λ k V (ψ + φ) = infAutOfEnd Λ k V ψ * infAutOfEnd Λ k V φ := sorry

/-- The map from `End_k(V)` to infinitesimal automorphisms is bijective. -/
theorem infAutOfEnd_bijective (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] : Function.Bijective (infAutOfEnd Λ k V) := sorry

/-- Endomorphisms of a finite-dimensional vector space form a finite-dimensional space. -/
theorem finiteDimensional_end (V : Type u) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] : FiniteDimensional k (Module.End k V) := inferInstance

end ArtinianLocalAlgCat.FiniteProjective
