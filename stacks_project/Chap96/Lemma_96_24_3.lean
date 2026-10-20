module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.AffineComparison
import StacksCheckRecall

/-!
# Lemma 96.24.3

For a category fibred in groupoids over `(Sch/S)_fppf`, the inclusion of the
associated affine `τ`-site into the associated `τ`-site is special
cocontinuous, and therefore identifies the corresponding sheaf topoi.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 96.24.3 (1): let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in
groupoids, and let `τ` be Zariski, étale, smooth, syntomic, or fppf. The
inclusion `affineInclusion X : 𝒳_affine,τ ⟶ 𝒳_τ` is special cocontinuous
from `associatedAffineTopology X τ` to `associatedTopology X τ`. -/
@[stacks 0H0B] #check
  (AlgebraicGeometry.GroupoidsOver.affineInclusion_isSpecialCocontinuous :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology),
      (GroupoidsOver.affineInclusion X).IsSpecialCocontinuous
        (X.associatedAffineTopology τ) (X.associatedTopology τ))

/- Lemma 96.24.3 (2): the special cocontinuous inclusion of (1) induces an
equivalence of topoi `Sh(𝒳_affine,τ) ⥤ Sh(𝒳_τ)` as the cocontinuous direct
image on sheaves of types `Type (u + 1)`. -/
@[stacks 0H0B] #check (AlgebraicGeometry.GroupoidsOver.affineInclusion_directImage_isEquivalence :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (τ : StandardTopology)
    [∀ P : (GroupoidsOver.Affine X)ᵒᵖ ⥤ Type (u + 1),
      (GroupoidsOver.affineInclusion X).op.HasPointwiseRightKanExtension P],
    ((GroupoidsOver.affineInclusion X).sheafPushforwardCocontinuous (Type (u + 1))
      (X.associatedAffineTopology τ) (X.associatedTopology τ)).IsEquivalence)
