module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech
import Mathlib.Tactic.CrossRefAttribute

/-!
# The augmented free Cech chain

This leaf owns the degree-zero augmentation of the free ringed-site Cech chain.  The chain is
formed in presheaves of modules, so its target is the presheaf module underlying the structure
ring, rather than a sheaf-module object.  Exactness of the augmented chain is deliberately not
asserted at this site-generic layer: it needs geometric hypotheses (for example, the open-set
extension-by-zero calculation used in Chapter 20).
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

namespace SheafOfModules.RingedSite.Cech

variable {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
variable (𝒪 : Sheaf K RingCat) (U : D) [HasFiniteProducts (Over U)]
variable {ι : Type u} (family : ι → Over U)

/-- Stacks 01EM: the degree-zero augmentation of the free Cech chain sends every distinguished
generator to `1` in the structure presheaf. -/
@[stacks 01EM "degree-zero augmentation of the free Cech chain"]
noncomputable def augmentation :
    (freeChain 𝒪 U family).X 0 ⟶ PresheafOfModules.unit 𝒪.obj :=
  eqToHom (freeChain_degree 𝒪 U family 0) ≫
    Sigma.desc fun i : Index U family 0 ↦
      PresheafOfModules.freeYonedaEquiv.symm
        (1 : 𝒪.obj.obj (op (intersection U family 0 i)))

/-- The degree-zero augmentation sends the canonical summand indexed by `i` to the unit
generator at the corresponding intersection. -/
@[stacks 01EM "augmentation on a Cech generator"]
theorem augmentation_comp_ι (i : Index U family 0) :
    Sigma.ι (fun j : Index U family 0 ↦ freeSummand 𝒪 U family 0 j) i ≫
        eqToHom (freeChain_degree 𝒪 U family 0).symm ≫ augmentation 𝒪 U family =
      PresheafOfModules.freeYonedaEquiv.symm
        (1 : 𝒪.obj.obj (op (intersection U family 0 i))) := sorry

end SheafOfModules.RingedSite.Cech
