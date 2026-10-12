/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.ExtensionByInitial
public import ReasLib.Topology.OpenCover.LocallyFinite
public import ReasLib.CategoryTheory.Limits.CoproductToProduct
public import stacks_project.Chap20.Open_cover_module_cech_explicit

/-!
# Locally finite Čech terms as coproducts

@stack 02FT
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens
open TopCat.Opens.Subspace

noncomputable section

universe u v w

namespace AlgebraicGeometry

/- Domain-style sampling for Remark 20.24.3:
- primary domain: locally finite coproduct-to-product comparisons for direct images from open
  subspaces, and the resulting comparison for module-valued Čech terms on a ringed space;
- sampled owner declarations:
  `modulePushforwardFromOpen`,
  `moduleRestrictionToOpen`,
  `SheafOfModules.pushforward`,
  `cechIntersection`,
  `openCoverModuleCechTerm`;
- best owner abstraction: the degree-`p` Čech term should remain the chapter owner
  `openCoverModuleCechTerm 𝒰 ℱ p`; the locally finite coproduct presentation is only a bridge to
  that owner, and the open-subspace restriction/pushforward pieces are derived from the existing
  Chapter 6/20 owners rather than new primitive data.

Source/core/bridge triage:
- `source-facing`: the locally finite isomorphism statements and the Čech-term comparison theorem;
- `core/canonical`: `Limits.coproductToProduct`, `openCoverModuleCechTerm`,
  `modulePushforwardFromOpen`,
  `moduleRestrictionToOpen`, `SheafOfModules.pushforward`, `cechIntersection`;
- `bridge/view`: `openPushforwardCoproductToProduct` and `openCoverModuleCechTermComparison`. -/

section

variable {X : TopCat.{u}} {ι : Type u}

/-- The family `i ↦ (j_i)_* ℱ i` of pushforwards from the open subspaces `U i ⊆ X`. -/
abbrev openPushforwardFamily
    (U : ι → Opens X)
    (ℱ : ∀ i, (space (U i)).Sheaf AddCommGrpCat.{u}) :
    ι → X.Sheaf AddCommGrpCat.{u} :=
  fun i ↦
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
      (inclusion (U i))).obj (ℱ i)

variable (U : ι → Opens X)
variable (ℱ : ∀ i, (space (U i)).Sheaf AddCommGrpCat.{u})
variable [HasCoproduct (openPushforwardFamily U ℱ)]
variable [HasProduct (openPushforwardFamily U ℱ)]

/-- The canonical map from the coproduct of pushed-forward abelian sheaves to the product of the
same family. -/
def openPushforwardCoproductToProduct :
    ∐ openPushforwardFamily U ℱ ⟶ ∏ᶜ openPushforwardFamily U ℱ :=
  coproductToProduct (openPushforwardFamily U ℱ)

/-- Helper for Remark 20.24.3: the locally finite comparison from the coproduct sheaf of
pushforwards to the product sheaf is an isomorphism. -/
private theorem locallyFinite_openPushforward_sheaf_comparison_isIso
    (U : ι → Opens X)
    (ℱ : ∀ i, (space (U i)).Sheaf AddCommGrpCat.{u})
    [HasCoproduct (openPushforwardFamily U ℱ)]
    [HasProduct (openPushforwardFamily U ℱ)]
    (hU : LocallyFinite (asSets U)) :
    IsIso (openPushforwardCoproductToProduct U ℱ) := by
  -- Proof sketch: compare the sheaf map with the underlying presheaf coproduct-to-product map,
  -- use local finiteness to reduce sections near each point to finitely many nonzero summands,
  -- and conclude that the canonical comparison is an isomorphism.
  let _ := hU
  sorry

-- Proof sketch: on the open `V`, sections of each summand are sections on `V ∩ U i`, and local
-- finiteness implies that every section of the coproduct sheaf has only finitely many nonzero
-- components near each point. Hence the canonical map from sections of the coproduct sheaf to the
-- product of the section groups is bijective.
/-- Remark 20.24.3: for a locally finite family of open subsets `U i ⊆ X` and abelian sheaves
`ℱ i` on the open subspaces `U i`, the canonical map from sections on `V` of the coproduct sheaf
`∐ i, (j_i)_* ℱ i` to the product of the section groups over `V` is an isomorphism. -/
@[stacks 02FT]
theorem locallyFinite_openPushforward_sections_comparison_isIso
    (hU : LocallyFinite (asSets U)) (V : Opens X) :
    IsIso (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op V)).map
      (openPushforwardCoproductToProduct U ℱ)) := by
  -- Once the sheaf comparison is known to be an isomorphism, evaluation on `V` preserves it.
  let _ : IsIso (openPushforwardCoproductToProduct U ℱ) :=
    locallyFinite_openPushforward_sheaf_comparison_isIso U ℱ hU
  let e : ∐ openPushforwardFamily U ℱ ≅ ∏ᶜ openPushforwardFamily U ℱ :=
    asIso (openPushforwardCoproductToProduct U ℱ)
  change IsIso (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op V)).map
    e.hom)
  infer_instance

-- Proof sketch: the previous sections computation holds for every open `V ⊆ X`. Since the
-- forgetful functor from abelian sheaves to presheaves reflects isomorphisms, the canonical map
-- from the coproduct of the pushed-forward sheaves to their product is therefore an isomorphism.
/-- The coproduct of a locally finite family of pushed-forward abelian sheaves identifies with the
product of the same family. -/
theorem openPushforwardCoproductToProduct_isIso_of_locallyFinite
    (hU : LocallyFinite (asSets U)) :
    IsIso (openPushforwardCoproductToProduct U ℱ) := by
  -- This is exactly the sheaf-level locally finite comparison isolated above.
  simpa using locallyFinite_openPushforward_sheaf_comparison_isIso U ℱ hU

end

namespace RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u}

local notation "ModX" => X.Modules

variable (𝒰 : ι → Opens X.carrier) (ℱ : ModX) (p : ℕ)
variable [HasProduct (openCoverModuleCechSummand 𝒰 ℱ p)]
variable [HasCoproduct (openCoverModuleCechSummand 𝒰 ℱ p)]

/-- The canonical map from the coproduct model of the degree-`p` Čech term to the canonical
owner `openCoverModuleCechTerm 𝒰 ℱ p`. -/
abbrev openCoverModuleCechTermComparison
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) (p : ℕ)
    [HasCoproduct (openCoverModuleCechSummand 𝒰 ℱ p)] :
    ∐ openCoverModuleCechSummand 𝒰 ℱ p ⟶ openCoverModuleCechTerm 𝒰 ℱ p :=
  coproductToProduct (openCoverModuleCechSummand 𝒰 ℱ p)

-- Proof sketch: apply the previous comparison theorem to the locally finite family of finite
-- intersections `U_{i₀} ∩ ⋯ ∩ U_{i_p}` and to the restricted sheaves on those intersections. This
-- turns the product Čech term into the corresponding coproduct term.
/-- The canonical comparison for the degree-`p` Čech term attached to a locally finite family of
open subsets is an isomorphism, so the product Čech term may be viewed as the corresponding
coproduct of pushforwards from the intersections. -/
theorem openCoverModuleCechTermComparison_isIso
    (𝒰 : ι → Opens X.carrier) (ℱ : ModX) (p : ℕ)
    [HasProduct (openCoverModuleCechSummand 𝒰 ℱ p)]
    [HasCoproduct (openCoverModuleCechSummand 𝒰 ℱ p)]
    (h𝒰lf : LocallyFinite (asSets 𝒰)) :
    IsIso (openCoverModuleCechTermComparison 𝒰 ℱ p) := by
  -- Route correction: transport the module comparison through the underlying additive-sheaf
  -- functor and reduce to the locally finite open-pushforward comparison for the family of
  -- intersections `σ ↦ cechIntersection 𝒰 σ`.
  let _ := h𝒰lf
  sorry

end RingedSpace

end AlgebraicGeometry
