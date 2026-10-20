module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Hom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Extension
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension

/-!
# Compatible maps of mixed-scalar module extensions

Along a first-order thickening, a morphism of mixed-scalar extensions over prescribed
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

namespace ModuleExtension

variable {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsFirstOrderThickening i]

/-- The infinitesimal comparison of a mixed-scalar extension, as an `𝒪_X`-module map
`ℐ ⊗ ℱ ⟶ 𝒦`. -/
noncomputable def infinitesimalMap_restrict (E : ModuleExtension i) :
    idealModule i ⊗ E.cokernel ⟶ E.kernel :=
  Modules.infinitesimalMap_restrict i
    (Modules.infinitesimalMap i E.ι E.π E.zero E.shortExact)

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

/-- Adding `π ≫ i_* α ≫ ι` to a compatible middle map preserves its kernel square. -/
theorem perturb_comm_ι (α : E.cokernel ⟶ E'.kernel) (φ' : CompatibleMap E E' ψ φ) :
    E.ι ≫ (φ'.hom + E.π ≫ (pushforward i).map α ≫ E'.ι) =
      (pushforward i).map ψ ≫ E'.ι := sorry

/-- Adding `π ≫ i_* α ≫ ι` to a compatible middle map preserves its cokernel square. -/
theorem perturb_comm_π (α : E.cokernel ⟶ E'.kernel) (φ' : CompatibleMap E E' ψ φ) :
    (φ'.hom + E.π ≫ (pushforward i).map α ≫ E'.ι) ≫ E'.π =
      E.π ≫ (pushforward i).map φ := sorry

/-- The action of `α : ℱ ⟶ ℒ` on a compatible middle map, by adding `π ≫ i_* α ≫ ι`. -/
def perturb (α : E.cokernel ⟶ E'.kernel) (φ' : CompatibleMap E E' ψ φ) :
    CompatibleMap E E' ψ φ where
  hom := φ'.hom + E.π ≫ (pushforward i).map α ≫ E'.ι
  comm_ι := perturb_comm_ι α φ'
  comm_π := perturb_comm_π α φ'

/-- The underlying morphism of a perturbed compatible map is the original morphism plus
`π ≫ i_* α ≫ ι`. -/
theorem perturb_hom (α : E.cokernel ⟶ E'.kernel) (φ' : CompatibleMap E E' ψ φ) :
    (perturb α φ').hom = φ'.hom + E.π ≫ (pushforward i).map α ≫ E'.ι := rfl

/-- Perturbing a compatible middle map by the zero morphism leaves it unchanged. -/
theorem perturb_zero (φ' : CompatibleMap E E' ψ φ) :
    perturb 0 φ' = φ' := sorry

/-- Perturbation by a sum is the composite of the two perturbations. -/
theorem perturb_add (α β : E.cokernel ⟶ E'.kernel) (φ' : CompatibleMap E E' ψ φ) :
    perturb (α + β) φ' = perturb α (perturb β φ') := sorry

/-- The difference of two compatible middle maps is killed by the cokernel projection. -/
theorem hom_sub_comp_π (φ' φ'' : CompatibleMap E E' ψ φ) :
    (φ''.hom - φ'.hom) ≫ E'.π = 0 := sorry

/-- After lifting the difference through the kernel inclusion of the target extension, the source
kernel inclusion composes to zero. -/
private theorem ι_comp_hom_sub_lift (φ' φ'' : CompatibleMap E E' ψ φ) [Mono E'.ι] :
    E.ι ≫ E'.shortExact.exact.lift (φ''.hom - φ'.hom) (hom_sub_comp_π φ' φ'') = 0 := sorry

/-- The unique `𝒪_X`-linear map `ℱ ⟶ ℒ` measuring the difference of two compatible middle
maps, obtained by factoring through the short exact sequences and applying the Hom equivalence. -/
noncomputable def difference (φ' φ'' : CompatibleMap E E' ψ φ) :
    E.cokernel ⟶ E'.kernel :=
  (fullyFaithful i (IsThickening.isHomeomorph_base i).isClosedEmbedding).homEquiv.symm
    (E.shortExact.exact.desc
      (E'.shortExact.exact.lift (φ''.hom - φ'.hom) (hom_sub_comp_π φ' φ''))
      (by exact ι_comp_hom_sub_lift φ' φ''))

/-- The difference between a compatible map and its perturbation is the perturbing morphism. -/
theorem difference_perturb (α : E.cokernel ⟶ E'.kernel) (φ' : CompatibleMap E E' ψ φ) :
    difference φ' (perturb α φ') = α := sorry

/-- Perturbing a compatible map by its difference with another recovers that other map. -/
theorem perturb_difference (φ' φ'' : CompatibleMap E E' ψ φ) :
    perturb (difference φ' φ'') φ' = φ'' := sorry

/-- Relative to one compatible middle map, perturbation by `Hom_{𝒪_X}(ℱ, ℒ)` parametrizes
all compatible middle maps. -/
noncomputable def perturbEquiv (φ' : CompatibleMap E E' ψ φ) :
    (E.cokernel ⟶ E'.kernel) ≃ CompatibleMap E E' ψ φ where
  toFun α := perturb α φ'
  invFun φ'' := difference φ' φ''
  left_inv α := difference_perturb α φ'
  right_inv φ'' := perturb_difference φ' φ''

end CompatibleMap

open CompatibleMap

/-- A compatible middle map makes the infinitesimal comparison square commute. -/
theorem infinitesimalMap_commSq
    (E E' : ModuleExtension i)
    (ψ : E.kernel ⟶ E'.kernel) (φ : E.cokernel ⟶ E'.cokernel)
    (φ' : CompatibleMap E E' ψ φ) :
    CommSq E.infinitesimalMap_restrict (tensorHom (𝟙 (idealModule i)) φ) ψ
      E'.infinitesimalMap_restrict := sorry

/-- For fixed endpoint maps, compatible middle maps form a principal homogeneous space under
`Hom_{𝒪_X}(ℱ, ℒ)` whenever the fiber is nonempty. -/
theorem compatibleMap_principalHomogeneous
    (E E' : ModuleExtension i)
    (ψ : E.kernel ⟶ E'.kernel) (φ : E.cokernel ⟶ E'.cokernel)
    (φ' φ'' : CompatibleMap E E' ψ φ) :
    ∃! α : E.cokernel ⟶ E'.kernel, perturb α φ' = φ'' := sorry

end ModuleExtension
end AlgebraicGeometry.RingedSpace.Hom
