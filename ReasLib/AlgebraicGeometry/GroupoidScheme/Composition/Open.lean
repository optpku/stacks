module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.FieldPoints
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Translation

/-!
# Composition with an open family of arrows

This module studies the image of the composition of an arbitrary family of arrows with an
open subscheme of the arrow scheme of a groupoid scheme over a field.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The pullback over the object scheme parametrizing arrows in the family `z` that are
composable with arrows in the open subscheme `W`. -/
def compOpenDomain {S : Scheme.{u}} (G : GroupoidScheme S) {Z : Scheme.{u}}
    (z : Z ⟶ G.R.left) (W : Scheme.Opens G.R.left) : Over S :=
  let ZOver : Over S := Over.mk (z ≫ G.R.hom)
  let zOver : ZOver ⟶ G.R := Over.homMk z
  let WOver : Over S := Over.mk (W.ι ≫ G.R.hom)
  let wOver : WOver ⟶ G.R := Over.homMk W.ι
  let hs := zOver ≫ G.s
  let ht := wOver ≫ G.t
  Limits.pullback hs ht

/-- The morphism that composes the family of arrows `z` with the open subscheme `W`. -/
def compOpen {S : Scheme.{u}} (G : GroupoidScheme S) {Z : Scheme.{u}}
    (z : Z ⟶ G.R.left) (W : Scheme.Opens G.R.left) : G.compOpenDomain z W ⟶ G.R :=
  let ZOver : Over S := Over.mk (z ≫ G.R.hom)
  let zOver : ZOver ⟶ G.R := Over.homMk z
  let WOver : Over S := Over.mk (W.ι ≫ G.R.hom)
  let wOver : WOver ⟶ G.R := Over.homMk W.ι
  let hs := zOver ≫ G.s
  let ht := wOver ≫ G.t
  G.compose
    (Limits.pullback.fst hs ht ≫ zOver)
    (Limits.pullback.snd hs ht ≫ wOver)
    ((Category.assoc _ _ _).trans
      ((Limits.pullback.condition).trans (Category.assoc _ _ _).symm))

/-- If the object scheme of a groupoid scheme is the spectrum of a field, then the image of
the composition of any arrow family with an open subscheme of the arrow scheme is open. -/
theorem isOpen_range_compOpen
    {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) {Z : Scheme.{u}}
    (z : Z ⟶ G.R.left) (W : Scheme.Opens G.R.left) :
    IsOpen (Set.range (G.compOpen z W).left.base) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  classical
  rcases hx with ⟨ξ, rfl⟩
  let ZOver : Over S := Over.mk (z ≫ G.R.hom)
  let zOver : ZOver ⟶ G.R := Over.homMk z
  let WOver : Over S := Over.mk (W.ι ≫ G.R.hom)
  let wOver : WOver ⟶ G.R := Over.homMk W.ι
  let hs := zOver ≫ G.s
  let ht := wOver ≫ G.t
  let r : G.R.left := z ((Limits.pullback.fst hs ht).left ξ)
  obtain ⟨K, _, ι, _, hLift⟩ :=
    G.existsAlgebraicallyClosedArrowLift eU r
  let g := G.fieldRestriction eU ι
  let G' := G.pullback g
  let φ := G.pullbackHom g
  let z' : Limits.pullback z φ.arrow.left ⟶ G'.R.left :=
    Limits.pullback.snd z φ.arrow.left
  let W' : Scheme.Opens G'.R.left := φ.arrow.left ⁻¹ᵁ W
  obtain ⟨r', hr', hsIso, htIso⟩ := hLift
  let z₀ : Z := (Limits.pullback.fst hs ht).left ξ
  let w₀ : W.toScheme := (Limits.pullback.snd hs ht).left ξ
  have hz₀ : z z₀ = r := rfl
  have hrz : φ.arrow.left r' = z z₀ := by
    simpa [r, z₀, hs, ht] using hr'
  have hφs : φ.arrow.left ≫ G.s.left = G'.s.left ≫ g.left := by
    change Over.Hom.left (G.pullbackArrow g) ≫ G.s.left =
      Over.Hom.left (G.toPreRelation.pullback g).s ≫ g.left
    exact congrArg Over.Hom.left (pullbackArrow_s G g)
  have hφt : φ.arrow.left ≫ G.t.left = G'.t.left ≫ g.left := by
    change Over.Hom.left (G.pullbackArrow g) ≫ G.t.left =
      Over.Hom.left (G.toPreRelation.pullback g).t ≫ g.left
    exact congrArg Over.Hom.left (pullbackArrow_t G g)
  have hW'ι : φ.arrow.left.resLE W W' le_rfl ≫ W.ι = W'.ι ≫ φ.arrow.left := by
    simp [W']
  have hφsurj : Function.Surjective φ.arrow.left := by
    -- Local instance justification (proof-local temporary data): expose canonical surjectivity to the pointwise scheme-morphism API.
    letI : Surjective φ.arrow.left := by
      simpa [g, φ] using
        (pullbackHom_arrow_surjective (G := G) (eU := eU) (ι := ι))
    exact Scheme.Hom.surjective φ.arrow.left
  obtain ⟨z₀', hz₀'fst, hz₀'snd⟩ :=
    AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := z) (g := φ.arrow.left) z₀ r' hrz.symm
  obtain ⟨w', hw'⟩ := hφsurj (W.ι w₀)
  obtain ⟨w₀', hw₀'⟩ : ∃ w₀' : W'.toScheme, W'.ι w₀' = w' := by
    refine ⟨⟨w', ?_⟩, rfl⟩
    change φ.arrow.left w' ∈ W
    simp [hw']
  let uIso' : G'.U.left ≅ Spec (CommRingCat.of K) := Iso.refl _
  -- Local instance justification (proof-local temporary data): expose the lifted source residue-field isomorphism to its comparison theorem.
  letI : IsIso (CommRingCat.ofHom
      (Scheme.Hom.ResidueField.mapOfSpec G'.s.left r')) := hsIso
  -- Local instance justification (proof-local temporary data): expose the lifted target residue-field isomorphism to its comparison theorem.
  letI : IsIso (CommRingCat.ofHom
      (Scheme.Hom.ResidueField.mapOfSpec G'.t.left r')) := htIso
  -- Local instance justification (proof-local temporary data): derive the source point-map isomorphism used to construct translation at `r'`.
  letI : IsIso (G'.R.left.fromSpecResidueField r' ≫ G'.s.left) := by
    have hSpec :
        Spec.map (CommRingCat.ofHom (Scheme.Hom.ResidueField.mapOfSpec G'.s.left r')) =
          G'.R.left.fromSpecResidueField r' ≫ G'.s.left :=
      Scheme.Hom.ResidueField.specMap_mapOfSpec G'.s.left r'
    exact hSpec ▸ (inferInstance : IsIso (Spec.map (CommRingCat.ofHom
      (Scheme.Hom.ResidueField.mapOfSpec G'.s.left r'))))
  -- Local instance justification (proof-local temporary data): derive the target point-map isomorphism proving translation at `r'` invertible.
  letI : IsIso (G'.R.left.fromSpecResidueField r' ≫ G'.t.left) := by
    have hSpec :
        Spec.map (CommRingCat.ofHom (Scheme.Hom.ResidueField.mapOfSpec G'.t.left r')) =
          G'.R.left.fromSpecResidueField r' ≫ G'.t.left :=
      Scheme.Hom.ResidueField.specMap_mapOfSpec G'.t.left r'
    exact hSpec ▸ (inferInstance : IsIso (Spec.map (CommRingCat.ofHom
      (Scheme.Hom.ResidueField.mapOfSpec G'.t.left r'))))
  -- Local instance justification (defeq pin): `uIso'` is the identity; pin the source composite to the derived point-map isomorphism.
  letI : IsIso (G'.R.left.fromSpecResidueField r' ≫ G'.s.left ≫ uIso'.hom) := by
    change IsIso (G'.R.left.fromSpecResidueField r' ≫ G'.s.left)
    infer_instance
  -- Local instance justification (defeq pin): `uIso'` is the identity; pin the target composite to the derived point-map isomorphism.
  letI : IsIso (G'.R.left.fromSpecResidueField r' ≫ G'.t.left ≫ uIso'.hom) := by
    change IsIso (G'.R.left.fromSpecResidueField r' ≫ G'.t.left)
    infer_instance
  let m : W'.toScheme ⟶ G'.R.left := W'.ι ≫ (G'.leftTranslationAt uIso' r').left
  let O' : Set G'.R.left := Set.range m.base
  let O : Set G.R.left := φ.arrow.left '' O'
  have hO'Open : IsOpen O' := by
    have hOpenMap : IsOpenMap ((G'.leftTranslationAt uIso' r').left.base) := by
      -- Local instance justification (proof-local temporary data): the translation theorem supplies this isomorphism only for the openness argument.
      letI : IsIso (G'.leftTranslationAt uIso' r') :=
        isIso_leftTranslationAt G' uIso' r'
      -- Local instance justification (proof-local temporary data): map the translation isomorphism through the forgetful functor to schemes.
      letI : IsIso ((Over.forget S).map (G'.leftTranslationAt uIso' r')) := by
        infer_instance
      -- Local instance justification (proof-local temporary data): expose the underlying scheme isomorphism to the universally-open API.
      letI : IsIso (G'.leftTranslationAt uIso' r').left := by
        simpa using
          (inferInstance : IsIso ((Over.forget S).map (G'.leftTranslationAt uIso' r')))
      let e : G'.R.left ≅ G'.R.left := asIso (G'.leftTranslationAt uIso' r').left
      have hUnivOpen : UniversallyOpen e.hom := by
        simpa using
          (MorphismProperty.RespectsIso.precomp (@UniversallyOpen) e.hom (𝟙 G'.R.left)
            (by infer_instance : UniversallyOpen (𝟙 G'.R.left)))
      exact Scheme.Hom.isOpenMap e.hom
    have hRangeOpen : IsOpen (Set.range W'.ι.base) := by
      simpa using (IsOpenImmersion.isOpen_range W'.ι)
    have hImage :
        Set.range m.base =
          (G'.leftTranslationAt uIso' r').left.base '' Set.range W'.ι.base := by
      ext y
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨W'.ι.base w, ⟨w, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨v, rfl⟩, rfl⟩
        exact ⟨v, rfl⟩
    change IsOpen (Set.range m.base)
    rw [hImage]
    exact hOpenMap _ hRangeOpen
  have hφOpen : IsOpenMap φ.arrow.left.base := by
    have hOpen : UniversallyOpen φ.arrow.left := by
      simpa [g, φ] using
        (pullbackHom_arrow_universallyOpen (G := G) (eU := eU) (ι := ι))
    exact Scheme.Hom.isOpenMap φ.arrow.left
  apply mem_nhds_iff.mpr
  refine ⟨O, ?_, hφOpen _ hO'Open, ?_⟩
  · intro y hy
    rcases hy with ⟨y', hy', rfl⟩
    rcases hy' with ⟨w₁', rfl⟩
    sorry
  · refine ⟨m w₀', ?_, ?_⟩
    · exact ⟨w₀', rfl⟩
    · sorry

end AlgebraicGeometry.GroupoidScheme
