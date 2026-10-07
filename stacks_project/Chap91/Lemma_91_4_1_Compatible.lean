module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Pushforward
public import stacks_project.Chap91.«91_4_0_1_Extension»
public import stacks_project.Chap91.Remark_91_4_7_Extension

/-!
# Compatible maps of mixed-scalar module extensions

Along a first-order thickening, a morphism of 08L4 mixed-scalar extensions over prescribed
endpoint maps is an `𝒪_{X'}`-linear middle map making the kernel and cokernel squares commute.
The `𝒪_X`-linear Hom-action on that fiber is by adding `π ≫ i_* α ≫ ι`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Preadditive
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModulePushforward.ClosedImmersion
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

/-- The underlying continuous map of a thickening of ringed spaces is a closed embedding. -/
theorem isClosedEmbedding_base {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsThickening i] :
    Topology.IsClosedEmbedding i.hom.base := sorry

/-- The structure-sheaf map of a first-order thickening is locally surjective. -/
instance commRingSheafPushforwardMap_isLocallySurjective
    {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i] :
    Sheaf.IsLocallySurjective (commRingSheafPushforwardMap i) := sorry

namespace ModuleExtension

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]

/-- The infinitesimal comparison of a mixed-scalar extension, as an `𝒪_X`-module map
`ℐ ⊗ ℱ ⟶ 𝒦`. -/
noncomputable def infinitesimalMap_restrict (E : ModuleExtension i) :
    idealModule i ⊗ E.cokernel ⟶ E.kernel :=
  Modules.infinitesimalMap_restrict i
    (Modules.infinitesimalMap i E.ι E.π E.extension.zero E.shortExact)

/-- The kernel inclusion of a mixed-scalar extension is a monomorphism. -/
instance instMono_ι (E : ModuleExtension i) : Mono E.ι :=
  E.shortExact.mono_f

/-- The cokernel projection of a mixed-scalar extension is an epimorphism. -/
instance instEpi_π (E : ModuleExtension i) : Epi E.π :=
  E.shortExact.epi_g

/-- An `𝒪_{X'}`-linear map of middle terms of mixed-scalar extensions along a first-order
thickening, compatible with given endpoint maps `ψ : 𝒦 ⟶ ℒ` and `φ : ℱ ⟶ 𝒢`. -/
@[ext]
structure CompatibleMap (E E' : ModuleExtension i)
    (ψ : E.kernel ⟶ E'.kernel) (φ : E.cokernel ⟶ E'.cokernel) where
  /-- The underlying morphism of middle `𝒪_{X'}`-modules. -/
  hom : E.middle ⟶ E'.middle
  /-- Compatibility with the inclusions of `i_* 𝒦` and `i_* ℒ`. -/
  comm_ι : E.ι ≫ hom = (pushforward i).map ψ ≫ E'.ι
  /-- Compatibility with the projections onto `i_* ℱ` and `i_* 𝒢`. -/
  comm_π : hom ≫ E'.π = E.π ≫ (pushforward i).map φ

namespace CompatibleMap

variable {E E' : ModuleExtension i}
variable {ψ : E.kernel ⟶ E'.kernel} {φ : E.cokernel ⟶ E'.cokernel}

/-- Assemble a compatible middle map from an `𝒪_{X'}`-linear morphism and the two commuting
squares with `ψ` and `φ`. -/
def of (hom : E.middle ⟶ E'.middle)
    (comm_ι : E.ι ≫ hom = (pushforward i).map ψ ≫ E'.ι)
    (comm_π : hom ≫ E'.π = E.π ≫ (pushforward i).map φ) :
    CompatibleMap E E' ψ φ where
  hom := hom
  comm_ι := comm_ι
  comm_π := comm_π

/-- A compatible middle map makes both endpoint squares commute. -/
theorem spec (φ' : CompatibleMap E E' ψ φ) :
    E.ι ≫ φ'.hom = (pushforward i).map ψ ≫ E'.ι ∧
      φ'.hom ≫ E'.π = E.π ≫ (pushforward i).map φ := sorry

/-- A middle map underlies a compatible map with endpoints `ψ` and `φ` if and only if both
endpoint squares commute. -/
theorem spec_iff (hom : E.middle ⟶ E'.middle) :
    (∃ φ' : CompatibleMap E E' ψ φ, φ'.hom = hom) ↔
      E.ι ≫ hom = (pushforward i).map ψ ≫ E'.ι ∧
        hom ≫ E'.π = E.π ≫ (pushforward i).map φ := sorry

/-- The morphism of underlying short complexes of `𝒪_{X'}`-modules attached to a compatible
middle map. -/
def toShortComplexHom (φ' : CompatibleMap E E' ψ φ) :
    E.toShortComplex ⟶ E'.toShortComplex where
  τ₁ := (pushforward i).map ψ
  τ₂ := φ'.hom
  τ₃ := (pushforward i).map φ
  comm₁₂ := φ'.comm_ι.symm
  comm₂₃ := φ'.comm_π

/-- The action of `α : ℱ ⟶ ℒ` on a compatible middle map, by adding `π ≫ i_* α ≫ ι`. -/
def perturb (α : E.cokernel ⟶ E'.kernel) (φ' : CompatibleMap E E' ψ φ) :
    CompatibleMap E E' ψ φ where
  hom := φ'.hom + E.π ≫ (pushforward i).map α ≫ E'.ι
  comm_ι := sorry
  comm_π := sorry

/-- The difference of two compatible middle maps is killed by the cokernel projection. -/
theorem hom_sub_comp_π (φ' φ'' : CompatibleMap E E' ψ φ) :
    (φ''.hom - φ'.hom) ≫ E'.π = 0 := sorry

/-- After lifting the difference through the kernel inclusion of the target extension, the
source kernel inclusion composes to zero. -/
theorem ι_comp_hom_sub_lift (φ' φ'' : CompatibleMap E E' ψ φ) [Mono E'.ι] :
    E.ι ≫ E'.shortExact.exact.lift (φ''.hom - φ'.hom) (hom_sub_comp_π φ' φ'') = 0 := sorry

/-- The unique `𝒪_X`-linear map `ℱ ⟶ ℒ` measuring the difference of two compatible middle
maps, obtained by factoring through the short exact sequences and applying the 08KS Hom
equivalence. -/
noncomputable def difference (φ' φ'' : CompatibleMap E E' ψ φ) :
    E.cokernel ⟶ E'.kernel :=
  (fullyFaithful i (isClosedEmbedding_base i)).homEquiv.symm
    (E.shortExact.exact.desc
      (E'.shortExact.exact.lift (φ''.hom - φ'.hom) (hom_sub_comp_π φ' φ''))
      (ι_comp_hom_sub_lift φ' φ''))

/-- Relative to one compatible middle map, perturbation by `Hom_{𝒪_X}(ℱ, ℒ)` parametrizes
all compatible middle maps. -/
noncomputable def perturbEquiv (φ' : CompatibleMap E E' ψ φ) :
    (E.cokernel ⟶ E'.kernel) ≃ CompatibleMap E E' ψ φ where
  toFun α := perturb α φ'
  invFun φ'' := difference φ' φ''
  left_inv := sorry
  right_inv := sorry

end CompatibleMap

end ModuleExtension

end AlgebraicGeometry.RingedSpace.Hom
