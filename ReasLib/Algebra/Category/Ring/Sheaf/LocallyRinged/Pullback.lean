module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally ringed sheaves under inverse image

Local ringedness is invariant under isomorphism and is preserved by the left-exact inverse-image
functor of a morphism of sites.  These facts are stated at the sheaf layer, independently of any
bundling as a ringed site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

section Iso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]
variable [J.HasSheafCompose (forget CommRingCat.{max u v})]

/-- Local ringedness is invariant under an isomorphism of commutative-ring sheaves. -/
@[stacks 04H7 "isomorphism invariance"]
theorem isLocallyRinged_iff_of_iso
    {𝒪 𝒪' : Sheaf J CommRingCat.{max u v}} (e : 𝒪 ≅ 𝒪') :
    𝒪.IsLocallyRinged ↔ 𝒪'.IsLocallyRinged := sorry

end Iso

section InverseImage

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [IsMorphismOfSites J K F]
variable [(F.sheafPushforwardContinuous CommRingCat.{max u v} J K).IsRightAdjoint]
variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify K (Type (max u v))]
variable [J.HasSheafCompose (forget CommRingCat.{max u v})]
variable [K.HasSheafCompose (forget CommRingCat.{max u v})]

/-- Lemma 18.40.5 (04H7) (1): inverse image along a morphism of sites preserves local
ringedness. -/
@[stacks 04H7 "(1)"]
theorem IsLocallyRinged.pullback
    (𝒪 : Sheaf J CommRingCat.{max u v}) [𝒪.IsLocallyRinged] :
    ((F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪).IsLocallyRinged := sorry

/-- Lemma 18.40.5 (04H7) (2): an inverse-image equivalence, followed by an isomorphism of
structure sheaves, preserves and reflects local ringedness. -/
@[stacks 04H7 "(2)"]
theorem isLocallyRinged_iff_of_pullback_equivalence
    [Functor.IsEquivalence (F.sheafPullback (Type (max u v)) J K)]
    {𝒪 : Sheaf J CommRingCat.{max u v}} {𝒪' : Sheaf K CommRingCat.{max u v}}
    (e : (F.sheafPullback CommRingCat.{max u v} J K).obj 𝒪 ≅ 𝒪') :
    𝒪.IsLocallyRinged ↔ 𝒪'.IsLocallyRinged := sorry

end InverseImage

end CategoryTheory.Sheaf
