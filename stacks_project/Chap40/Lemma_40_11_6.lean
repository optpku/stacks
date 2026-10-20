module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.SchemeTheoreticImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.Hom

/- Lemma 40.11.6: for an identity-on-objects morphism of groupoid schemes over a field
whose arrow map is quasi-compact, the scheme-theoretic arrow image admits composition,
identity, and inverse maps satisfying the groupoid laws with the canonical restricted
source and target maps. -/
@[stacks 04QA] #check (AlgebraicGeometry.GroupoidScheme.Hom.image :
  ∀ {S : Scheme.{u}} {k : Type u} [Field k] {G₁ G₂ : GroupoidScheme S}
    (eU : Spec (CommRingCat.of k) ≅ G₁.U.left) (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) [QuasiCompact f.arrow.left],
    ∃ c : pullback (imageSource f) (imageTarget f) ⟶ Scheme.Hom.imageOver f.arrow,
      ∃ e : G₂.U ⟶ Scheme.Hom.imageOver f.arrow,
        ∃ i : Scheme.Hom.imageOver f.arrow ⟶ Scheme.Hom.imageOver f.arrow,
          IsImageGroupoid f c e i)

end AlgebraicGeometry.GroupoidScheme.Hom
