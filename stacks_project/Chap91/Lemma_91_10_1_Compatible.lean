module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap91.«91_10_0_1_Extension»

/-!
# Compatible maps of mixed-scalar extensions

On a same-site first-order thickening π : 𝒪' ⟶ 𝒪, this leaf owns the type of 𝒪'-module
maps ℱ' ⟶ 𝒢' compatible with fixed 𝒪-module maps φ : ℱ ⟶ 𝒢 and ψ : 𝒦 ⟶ ℒ, together
with the additive action of Hom_𝒪(ℱ, ℒ).
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite
namespace FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable (F G : Extension π) (φ : F.quot ⟶ G.quot) (ψ : F.kernel ⟶ G.kernel)

/-- An 𝒪'-module map ℱ' ⟶ 𝒢' compatible with given 𝒪-module maps φ : ℱ ⟶ 𝒢 and
ψ : 𝒦 ⟶ ℒ. -/
structure CompatibleMap where
  /-- The underlying 𝒪'-module morphism ℱ' ⟶ 𝒢'. -/
  hom : F.middle ⟶ G.middle
  /-- Compatibility with the inclusions of the kernels 𝒦 ⟶ ℒ. -/
  comm_ι : F.ι ≫ hom = (restrictionAlong π).map ψ ≫ G.ι
  /-- Compatibility with the projections onto the quotients ℱ ⟶ 𝒢. -/
  comm_p : hom ≫ G.p = F.p ≫ (restrictionAlong π).map φ

namespace CompatibleMap

/-- Assemble a compatible 𝒪'-module map from a middle morphism and its two commuting squares. -/
def of (hom : F.middle ⟶ G.middle)
    (hι : CommSq F.ι ((restrictionAlong π).map ψ) hom G.ι)
    (hp : CommSq hom F.p G.p ((restrictionAlong π).map φ)) :
    CompatibleMap F G φ ψ where
  hom := hom
  comm_ι := hι.w
  comm_p := hp.w

/-- A compatible map is a morphism of mixed-scalar short complexes with the restricted
endpoint maps. -/
theorem spec (f : CompatibleMap F G φ ψ) :
    CommSq F.ι ((restrictionAlong π).map ψ) f.hom G.ι ∧
      CommSq f.hom F.p G.p ((restrictionAlong π).map φ) := sorry

/-- The kernel square for the Hom_𝒪(ℱ, ℒ)-translate of a compatible map. -/
theorem vadd_comm_ι (α : F.quot ⟶ G.kernel) (f : CompatibleMap F G φ ψ) :
    F.ι ≫ (f.hom + (F.p ≫ (restrictionAlong π).map α ≫ G.ι)) =
      (restrictionAlong π).map ψ ≫ G.ι := sorry

/-- The quotient square for the Hom_𝒪(ℱ, ℒ)-translate of a compatible map. -/
theorem vadd_comm_p (α : F.quot ⟶ G.kernel) (f : CompatibleMap F G φ ψ) :
    (f.hom + (F.p ≫ (restrictionAlong π).map α ≫ G.ι)) ≫ G.p =
      F.p ≫ (restrictionAlong π).map φ := sorry

/-- Translate a compatible map by an 𝒪-module morphism α : ℱ ⟶ ℒ. -/
def vadd (α : F.quot ⟶ G.kernel) (f : CompatibleMap F G φ ψ) :
    CompatibleMap F G φ ψ where
  hom := f.hom + (F.p ≫ (restrictionAlong π).map α ≫ G.ι)
  comm_ι := vadd_comm_ι F G φ ψ α f
  comm_p := vadd_comm_p F G φ ψ α f

/-- The underlying middle map of a Hom_𝒪(ℱ, ℒ)-translate. -/
theorem vadd_hom (α : F.quot ⟶ G.kernel) (f : CompatibleMap F G φ ψ) :
    (vadd F G φ ψ α f).hom = f.hom + (F.p ≫ (restrictionAlong π).map α ≫ G.ι) := sorry

/-- The kernel square of the associated short-complex morphism. -/
theorem toHom_comm₁₂ (f : CompatibleMap F G φ ψ) :
    (restrictionAlong π).map ψ ≫ G.ι = F.ι ≫ f.hom := sorry

/-- The quotient square of the associated short-complex morphism. -/
theorem toHom_comm₂₃ (f : CompatibleMap F G φ ψ) :
    f.hom ≫ G.p = F.p ≫ (restrictionAlong π).map φ := sorry

/-- The morphism of mixed-scalar short complexes with restricted endpoints φ and ψ. -/
def toHom (f : CompatibleMap F G φ ψ) : shortComplex F ⟶ shortComplex G :=
  ShortComplex.homMk ((restrictionAlong π).map ψ) f.hom ((restrictionAlong π).map φ)
    (toHom_comm₁₂ F G φ ψ f) (toHom_comm₂₃ F G φ ψ f)

/-- Any two compatible maps differ by a unique 𝒪-module morphism ℱ ⟶ ℒ. -/
theorem existsUnique_vsub [Sheaf.IsLocallySurjective π]
    (f g : CompatibleMap F G φ ψ) :
    ∃! α : F.quot ⟶ G.kernel, vadd F G φ ψ α g = f := sorry

end CompatibleMap

end FirstOrderThickening
end SheafOfModules.RingedSite
