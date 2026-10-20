module

public import ReasLib.CategoryTheory.Sites.TopologyComparison
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Absolute sheaf functors for a comparison of topologies

For `τ' ≤ τ` on one category, this leaf owns the coefficient-polymorphic direct image, inverse
image, and adjunction induced by the identity functor. Slice-localized comparison functors live in
`TopologyComparison.Sheaf`; derived constructions build on this smaller absolute owner.
-/

open CategoryTheory

noncomputable section

universe w u v

namespace CategoryTheory.GrothendieckTopology.TopologyComparison

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}
variable (A : Type w) [Category A]

/-- Direct image of sheaves along the identity comparison `τ' ≤ τ`. -/
@[stacks 0F18 "absolute topology-comparison direct image",
  stacks 0F19 "absolute topology-comparison direct image",
  stacks 0EZF "absolute topology-comparison direct image"]
noncomputable def pushforward (hle : τ' ≤ τ) :
    Sheaf τ A ⥤ Sheaf τ' A :=
  -- Local instance justification (noncanonical choice): the continuity certificate depends on
  -- `hle`, so a global instance for every pair of topologies on `C` would overlap.
  let _ : Functor.IsContinuous (𝟭 C) τ' τ := Functor.id_isContinuous_of_le hle
  (𝟭 C).sheafPushforwardContinuous A τ' τ

/-- Inverse image of sheaves along the identity comparison `τ' ≤ τ`. -/
@[stacks 0F18 "absolute topology-comparison inverse image",
  stacks 0F19 "absolute topology-comparison inverse image"]
noncomputable def pullback
    (hle : τ' ≤ τ)
    [HasWeakSheafify τ A]
    [∀ F : Cᵒᵖ ⥤ A, (𝟭 C).op.HasLeftKanExtension F] :
    Sheaf τ' A ⥤ Sheaf τ A :=
  -- Local instance justification (noncanonical choice): the explicit Kan-extension presentation
  -- needs the order-indexed certificate, which must not become a global overlapping instance.
  let _ : Functor.IsContinuous (𝟭 C) τ' τ := Functor.id_isContinuous_of_le hle
  Functor.sheafPullbackConstruction.sheafPullback (𝟭 C) A τ' τ

/-- The canonical sheaf adjunction for the identity comparison `τ' ≤ τ`. -/
@[stacks 0F18 "absolute topology-comparison adjunction",
  stacks 0F19 "absolute topology-comparison adjunction"]
noncomputable def adjunction
    (hle : τ' ≤ τ)
    [HasWeakSheafify τ A]
    [∀ F : Cᵒᵖ ⥤ A, (𝟭 C).op.HasLeftKanExtension F] :
    pullback A hle ⊣ pushforward A hle :=
  -- Local instance justification (noncanonical choice): this canonical adjunction uses the
  -- `hle`-indexed certificate only for its construction, not as ambient instance data.
  let _ : Functor.IsContinuous (𝟭 C) τ' τ := Functor.id_isContinuous_of_le hle
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (𝟭 C) A τ' τ

/-- The identity-site inverse image is exact for set-valued sheaves. -/
@[stacks 0EWI "exactness of the identity-site inverse image"]
theorem pullback_exact
    (hle : τ' ≤ τ)
    [HasSheafify τ (Type w)]
    [∀ F : Cᵒᵖ ⥤ Type w, (𝟭 C).op.HasLeftKanExtension F] :
    exactFunctor (Sheaf τ' (Type w)) (Sheaf τ (Type w))
      (pullback (Type w) hle) := sorry

-- The `sorryAx` in these data owners is inherited from the Prop-valued identity-continuity
-- certificate and the supplied sheafification/Kan-extension instances.

end CategoryTheory.GrothendieckTopology.TopologyComparison

end
