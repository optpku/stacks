module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.SchemeTheoreticImage

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.Hom

/- The image-groupoid laws bundle into the canonical groupoid-scheme structure. -/
#check (AlgebraicGeometry.GroupoidScheme.Hom.IsImageGroupoid.toGroupoidScheme :
  ∀ {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S} {f : Hom G₁ G₂}
    {c : pullback (imageSource f) (imageTarget f) ⟶ Scheme.Hom.imageOver f.arrow}
    {e : G₂.U ⟶ Scheme.Hom.imageOver f.arrow}
    {i : Scheme.Hom.imageOver f.arrow ⟶ Scheme.Hom.imageOver f.arrow},
    IsImageGroupoid f c e i → GroupoidScheme S)

/- The image-groupoid existence theorem remains available through this compatibility module. -/
#check (AlgebraicGeometry.GroupoidScheme.Hom.image :
  ∀ {S : Scheme.{u}} {k : Type u} [Field k] {G₁ G₂ : GroupoidScheme S}
    (eU : Spec (CommRingCat.of k) ≅ G₁.U.left) (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (_ : f.IsIdentityOnObjects hU) [QuasiCompact f.arrow.left],
    ∃ c : pullback (imageSource f) (imageTarget f) ⟶ Scheme.Hom.imageOver f.arrow,
      ∃ e : G₂.U ⟶ Scheme.Hom.imageOver f.arrow,
        ∃ i : Scheme.Hom.imageOver f.arrow ⟶ Scheme.Hom.imageOver f.arrow,
          IsImageGroupoid f c e i)

end AlgebraicGeometry.GroupoidScheme.Hom
