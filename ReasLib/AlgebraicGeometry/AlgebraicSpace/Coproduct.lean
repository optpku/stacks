/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Topology.Clopen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Coproducts of algebraic spaces

This module records that a small coproduct of algebraic spaces, formed as the coproduct in
fppf sheaves of their functors of points, is again an algebraic space. Mathlib sheafification of
`Type u`-valued presheaves on `Over S` lands in `Type (u + 1)`, so the sheaf coproduct is given
explicitly as a `Type u`-valued presheaf: a section over `T` is a pairwise disjoint, jointly
covering family of open-and-closed subschemes of `T`, indexed by all of `Shrink I` (including
empty pieces), together with a section of the corresponding summand on each piece.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite Classical

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The empty open subscheme of a scheme is an empty scheme. -/
instance instIsEmptyBotOpen {X : Scheme.{u}} : IsEmpty (⊥ : X.Opens).toScheme :=
  inferInstanceAs (IsEmpty (∅ : Set X))

/-- The empty open of a test scheme over `S` is an empty object of `Over S`. -/
instance instIsEmptyBotOpenOver {S : Scheme.{u}} (T : Over S) :
    IsEmpty (Over.mk ((⊥ : T.left.Opens).ι ≫ T.hom)).left :=
  inferInstanceAs (IsEmpty (⊥ : T.left.Opens).toScheme)

/-- The unique section of an algebraic space over an empty scheme over `S`. -/
def emptySection {S : Scheme.{u}} (F : AlgebraicSpace S) (T : Over S) [IsEmpty T.left] :
    F.functorOfPoints.obj (op T) :=
  (Types.isTerminalEquivUnique _
      (Sheaf.isTerminalOfBotCover { obj := F.functorOfPoints, property := F.isSheaf } T
        ((Scheme.fppfTopology.mem_over_iff (⊥ : Sieve T)).mpr
          ((Sieve.overEquiv T).map_bot.symm ▸
            (Scheme.bot_mem_grothendieckTopology T.left :
              ⊥ ∈ Scheme.fppfTopology T.left))))).default

/-- A section of the sheaf coproduct of a small family of algebraic spaces over a test scheme `T`:
a pairwise disjoint, jointly covering family of open-and-closed pieces of `T`, indexed by every
element of `Shrink I` (including empty pieces), together with a section of the corresponding
summand on each piece. Empty pieces carry the unique section of an fppf sheaf on the empty
scheme. -/
structure CoproductSection {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    (F : I → AlgebraicSpace S) (T : Over S) where
  /-- The open-and-closed piece of `T` labelled by an index in `Shrink I`. -/
  piece : Shrink.{u} I → T.left.Opens
  /-- Each piece is clopen in `T`. -/
  isClopen : ∀ i, IsClopen (piece i : Set T.left)
  /-- Distinct pieces are disjoint. -/
  pairwiseDisjoint :
    ∀ i j, i ≠ j → Disjoint (piece i : Set T.left) (piece j)
  /-- The pieces jointly cover `T`. -/
  iSup_eq_top : (⨆ i, piece i) = ⊤
  /-- A section of the corresponding algebraic space over each piece, including empty pieces. -/
  summandSection : ∀ i,
    (F ((equivShrink.{u} I).symm i)).functorOfPoints.obj
      (op (Over.mk ((piece i).ι ≫ T.hom)))

/-- The coproduct section over `T` supported on a single summand `i`, with piece `⊤` on that
summand and the empty piece (carrying the unique empty-scheme section) on every other summand. -/
def CoproductSection.single {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    (F : I → AlgebraicSpace S) (T : Over S) (i : I)
    (s : (F i).functorOfPoints.obj (op T)) : CoproductSection F T :=
  let piece : Shrink.{u} I → T.left.Opens :=
    fun j ↦ if j = equivShrink.{u} I i then ⊤ else ⊥
  let laws : (∀ j, IsClopen (piece j : Set T.left)) ∧
      (∀ j k, j ≠ k → Disjoint (piece j : Set T.left) (piece k)) ∧
        (⨆ j, piece j) = ⊤ := sorry
  { piece := piece
    isClopen := laws.1
    pairwiseDisjoint := laws.2.1
    iSup_eq_top := laws.2.2
    summandSection := fun j ↦
      if h : j = equivShrink.{u} I i then
        Eq.mp
          (congrArg
            (fun U : T.left.Opens ↦
              (F ((equivShrink.{u} I).symm j)).functorOfPoints.obj
                (op (Over.mk (U.ι ≫ T.hom))))
            (if_pos h).symm)
          (Eq.mp
            (congrArg
              (fun k : I ↦
                (F k).functorOfPoints.obj
                  (op (Over.mk ((⊤ : T.left.Opens).ι ≫ T.hom))))
              (h ▸ (equivShrink.{u} I).symm_apply_apply i).symm)
            ((F i).functorOfPoints.map
              (Over.homMk ((⊤ : T.left.Opens).ι) :
                  Over.mk ((⊤ : T.left.Opens).ι ≫ T.hom) ⟶ T).op
              s))
      else
        Eq.mp
          (congrArg
            (fun U : T.left.Opens ↦
              (F ((equivShrink.{u} I).symm j)).functorOfPoints.obj
                (op (Over.mk (U.ι ≫ T.hom))))
            (if_neg h).symm)
          (emptySection (F ((equivShrink.{u} I).symm j))
            (Over.mk ((⊥ : T.left.Opens).ι ≫ T.hom))) }

/-- Pull back a coproduct section along a morphism of schemes over `S`, taking the preimage of
every piece (including empty pieces). -/
def CoproductSection.restrict {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {F : I → AlgebraicSpace S} {X Y : Over S} (f : Y ⟶ X) (s : CoproductSection F X) :
    CoproductSection F Y :=
  let laws : (⨆ i, f.left ⁻¹ᵁ s.piece i) = ⊤ ∧
      (∀ i, (f.left ∣_ s.piece i) ≫ ((s.piece i).ι ≫ X.hom) =
        (f.left ⁻¹ᵁ s.piece i).ι ≫ Y.hom) := sorry
  { piece := fun i ↦ f.left ⁻¹ᵁ s.piece i
    isClopen := fun i ↦ (s.isClopen i).preimage f.left.continuous
    pairwiseDisjoint := fun i j hij ↦
      (s.pairwiseDisjoint i j hij).preimage (f.left : Y.left → X.left)
    iSup_eq_top := laws.1
    summandSection := fun i ↦
      (F ((equivShrink.{u} I).symm i)).functorOfPoints.map
        (Over.homMk (f.left ∣_ s.piece i) (laws.2 i)).op (s.summandSection i) }

/-- A coproduct section gives clopen, pairwise disjoint pieces covering the test scheme. -/
theorem CoproductSection.spec {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {F : I → AlgebraicSpace S} {T : Over S} (s : CoproductSection F T) :
    (∀ i, IsClopen (s.piece i : Set T.left)) ∧
      (∀ i j, i ≠ j → Disjoint (s.piece i : Set T.left) (s.piece j)) ∧
        (⨆ i, s.piece i) = ⊤ := sorry

/-- The covering sieve on `T` generated by the clopen pieces of a coproduct section. -/
theorem CoproductSection.ofArrows_mem {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {F : I → AlgebraicSpace S} {T : Over S} (s : CoproductSection F T) :
    Sieve.ofArrows (fun i : Shrink.{u} I ↦ Over.mk ((s.piece i).ι ≫ T.hom))
      (fun i ↦ Over.homMk (s.piece i).ι rfl) ∈ Scheme.fppfTopology.over S T := sorry

/-- Glue the images of a coproduct section under a family of morphisms into a sheaf. -/
def CoproductSection.desc {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {F : I → AlgebraicSpace S} {P : AlgebraicSpace S} {T : Over S}
    (p : ∀ i, F i ⟶ P) (s : CoproductSection F T) : P.functorOfPoints.obj (op T) :=
  (P.isSheaf.amalgamateOfArrows
      (fun i : Shrink.{u} I ↦ Over.homMk (s.piece i).ι rfl) s.ofArrows_mem
      (fun i ↦ ↾fun (_ : PUnit.{u + 1}) ↦
        (p ((equivShrink.{u} I).symm i)).app (op (Over.mk ((s.piece i).ι ≫ T.hom)))
          (s.summandSection i))
      sorry)
    PUnit.unit

/-- Comparison of the forgetful image of an `Over S` coproduct with the coproduct of the
underlying schemes. -/
def coproductForgetIso {S : Scheme.{u}} {I : Type v} [Small.{u} I] (U : I → Over S) :
    (∐ U).left ≅ ∐ fun j : I ↦ (U j).left :=
  preservesColimitIso (Over.forget S) (Discrete.functor U) ≪≫
    HasColimit.isoOfNatIso Discrete.natIsoFunctor

/-- The clopen image of the `i`-th scheme-coproduct summand, pulled back along the forgetful
comparison `(∐ U).left ≅ ∐ (U i).left`. -/
def CoproductSection.sigmaPiece {S : Scheme.{u}} {I : Type v} [Small.{u} I] (U : I → Over S)
    (i : I) : (∐ U).left.Opens :=
  (coproductForgetIso U).hom ⁻¹ᵁ ((sigmaOpenCover fun j : I ↦ (U j).left).f i).opensRange

/-- The identification of the `i`-th clopen piece of `∐ U` with the scheme `U i`. -/
def CoproductSection.sigmaPieceHom {S : Scheme.{u}} {I : Type v} [Small.{u} I] (U : I → Over S)
    (i : I) :
    (Over.mk ((CoproductSection.sigmaPiece U i).ι ≫ (∐ U).hom)).left ⟶ (U i).left :=
  let f := (sigmaOpenCover fun j : I ↦ (U j).left).f i
  (coproductForgetIso U).hom ∣_ f.opensRange ≫
    (IsOpenImmersion.isoOfRangeEq f f.opensRange.ι
      ((Scheme.Hom.coe_opensRange f).trans (Scheme.Opens.range_ι f.opensRange).symm)).inv

/-- The coproduct section over `∐ U` whose pieces are the clopen images of the scheme coproduct
summands, with summand sections obtained from `p` by transporting along those identifications. -/
def CoproductSection.ofEtaleAtlas {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {F : I → AlgebraicSpace S} {U : I → Over S}
    (p : ∀ i, yoneda.obj (U i) ⟶ (F i).functorOfPoints) :
    CoproductSection F (∐ U) :=
  let piece : Shrink.{u} I → (∐ U).left.Opens :=
    fun j ↦ CoproductSection.sigmaPiece U ((equivShrink.{u} I).symm j)
  let laws : (∀ j, IsClopen (piece j : Set (∐ U).left)) ∧
      (∀ j k, j ≠ k → Disjoint (piece j : Set (∐ U).left) (piece k)) ∧
        (⨆ j, piece j) = ⊤ ∧
          (∀ j, CoproductSection.sigmaPieceHom U ((equivShrink.{u} I).symm j) ≫
            (U ((equivShrink.{u} I).symm j)).hom = (piece j).ι ≫ (∐ U).hom) := sorry
  { piece := piece
    isClopen := laws.1
    pairwiseDisjoint := laws.2.1
    iSup_eq_top := laws.2.2.1
    summandSection := fun j ↦
      (F ((equivShrink.{u} I).symm j)).functorOfPoints.map
        (Over.homMk (CoproductSection.sigmaPieceHom U ((equivShrink.{u} I).symm j))
          (laws.2.2.2 j)).op
        (yonedaEquiv (p ((equivShrink.{u} I).symm j))) }

/-- The pointwise coproduct of the functors of points of a small family of algebraic spaces.
This is generally not an fppf sheaf; the sheaf coproduct is `coproductSheaf`. -/
def coproductPresheaf {S : Scheme.{u}} {I : Type v} [Small.{u} I] (F : I → AlgebraicSpace S) :
    (Over S)ᵒᵖ ⥤ Type u :=
  ∐ fun i ↦ (F i).functorOfPoints

/-- The fppf sheaf coproduct of a small family of algebraic spaces, as an explicit `Type u`-valued
presheaf on `Over S`. A section over `T` is a clopen partition of `T` indexed by all of `Shrink I`
together with a summand section on each piece, including empty pieces. -/
def coproductSheaf {S : Scheme.{u}} {I : Type v} [Small.{u} I] (F : I → AlgebraicSpace S) :
    (Over S)ᵒᵖ ⥤ Type u :=
  let map : ∀ {X Y : (Over S)ᵒᵖ}, (X ⟶ Y) →
      (CoproductSection F (unop X) ⟶ CoproductSection F (unop Y)) :=
    fun f ↦ ↾fun s ↦ CoproductSection.restrict (unop f) s
  let laws : (∀ X, map (𝟙 X) = 𝟙 (CoproductSection F (unop X))) ∧
      (∀ {X Y Z : (Over S)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z),
        map (f ≫ g) = map f ≫ map g) := sorry
  { obj := fun T ↦ CoproductSection F (unop T)
    map := map
    map_id := laws.1
    map_comp := laws.2 }

/-- The algebraic space whose functor of points is the sheaf coproduct of a small family of
algebraic spaces. The size hypothesis that `I` and the `F i` are not too large is encoded by
`[Small.{u} I]`. -/
def coproduct {S : Scheme.{u}} {I : Type v} [Small.{u} I] (F : I → AlgebraicSpace S) :
    AlgebraicSpace S :=
  let laws : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (coproductSheaf F) ∧
      yoneda.relativelyRepresentable (Limits.diag (coproductSheaf F)) ∧
        (∃ (U : Over S) (p : yoneda.obj U ⟶ coproductSheaf F),
          MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p) := sorry
  ofFunctor (coproductSheaf F) laws.1 laws.2.1 laws.2.2

/-- The canonical inclusion of a summand into the sheaf coproduct of algebraic spaces. -/
def coproductι {S : Scheme.{u}} {I : Type v} [Small.{u} I] (F : I → AlgebraicSpace S) (i : I) :
    F i ⟶ coproduct F where
  app T := ↾fun s ↦ CoproductSection.single F (unop T) i s
  naturality := sorry

/-- The canonical map from the pointwise presheaf coproduct into the sheaf coproduct. -/
def coproductPresheafToSheaf {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    (F : I → AlgebraicSpace S) : coproductPresheaf F ⟶ coproductSheaf F :=
  Sigma.desc fun i ↦ coproductι F i

/-- The morphism `coproduct G ⟶ P` induced by a family of morphisms from the summands, obtained by
gluing along the clopen partition of a coproduct section. -/
def coproductDesc {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {G : I → AlgebraicSpace S} {P : AlgebraicSpace S} (p : ∀ i, G i ⟶ P) :
    coproduct G ⟶ P where
  app T := ↾fun s ↦ CoproductSection.desc p s
  naturality := sorry

/-- Postcomposing the coproduct inclusions with `coproductDesc p` recovers `p`. -/
theorem coproductι_desc {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {G : I → AlgebraicSpace S} {P : AlgebraicSpace S} (p : ∀ i, G i ⟶ P) (i : I) :
    coproductι G i ≫ coproductDesc p = p i := sorry

/-- The functor of points of `coproduct F` is the explicit sheaf coproduct `coproductSheaf F`. -/
@[simp]
theorem coproduct_functorOfPoints {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    (F : I → AlgebraicSpace S) :
    (coproduct F).functorOfPoints = coproductSheaf F := sorry

/-- The coproduct of algebraic spaces is an fppf sheaf with representable diagonal and a
representable étale locally-surjective atlas. -/
theorem coproduct_spec {S : Scheme.{u}} {I : Type v} [Small.{u} I] (F : I → AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (coproduct F).functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag (coproduct F).functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ (coproduct F).functorOfPoints),
          MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- Every family of maps from the summands into an fppf sheaf extends uniquely to the
explicit sheaf coproduct. -/
theorem coproductSheaf_universal {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    (F : I → AlgebraicSpace S) (P : (Over S)ᵒᵖ ⥤ Type u)
    (h_sheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) P)
    (p : ∀ i, (F i).functorOfPoints ⟶ P) :
    ∃! q : coproductSheaf F ⟶ P,
      ∀ i, NatTrans.vcomp (coproductι F i) q = p i := sorry

/-- The atlas map `yoneda.obj (∐ U) ⟶ (coproduct F).functorOfPoints` obtained by pulling back the
clopen decomposition of `∐ U` along the given étale surjections `U i ⟶ F i`. -/
def coproductEtaleAtlas {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    (F : I → AlgebraicSpace S) {U : I → Over S}
    (p : ∀ i, yoneda.obj (U i) ⟶ (F i).functorOfPoints) :
    yoneda.obj (∐ U) ⟶ (coproduct F).functorOfPoints :=
  yonedaEquiv.symm (CoproductSection.ofEtaleAtlas p)

/-- If `U i ⟶ F i` are surjective étale and `∐ U i` exists in `Over S`, then the map
`coproductEtaleAtlas` obtained by pulling back the clopen decomposition of `∐ U` is a
surjective étale atlas of the coproduct. -/
theorem coproduct_of_etale_atlas {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    (F : I → AlgebraicSpace S) {U : I → Over S}
    (p : ∀ i, yoneda.obj (U i) ⟶ (F i).functorOfPoints)
    (h_etale : ∀ i, (MorphismProperty.over (@Etale)).presheaf (p i))
    (h_surj : ∀ i, Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (p i)) :
    (MorphismProperty.over (@Etale)).presheaf (coproductEtaleAtlas F p) ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (coproductEtaleAtlas F p) := sorry

/-- Algebraic spaces over `S` admit coproducts indexed by `Small.{u}` types, with coproduct object
`coproduct` and inclusions `coproductι`. The instance is stated as colimits of discrete shape
with `Small.{u} I` controlling the universe of the scheme coproduct. -/
instance hasCoproductsOfShape {S : Scheme.{u}} {I : Type v} [Small.{u} I] :
    HasColimitsOfShape (Discrete I) (AlgebraicSpace S) where
  has_colimit F :=
    let cocone : Cocone F :=
      { pt := coproduct fun i ↦ F.obj ⟨i⟩
        ι := Discrete.natTrans fun i ↦ coproductι (fun j ↦ F.obj ⟨j⟩) i.as }
    let desc : ∀ s : Cocone F, cocone.pt ⟶ s.pt :=
      fun s ↦ coproductDesc fun i ↦ s.ι.app ⟨i⟩
    let laws : (∀ (s : Cocone F) (j : Discrete I), cocone.ι.app j ≫ desc s = s.ι.app j) ∧
        (∀ (s : Cocone F) (m : cocone.pt ⟶ s.pt),
          (∀ j : Discrete I, cocone.ι.app j ≫ m = s.ι.app j) → m = desc s) := sorry
    HasColimit.mk
      { cocone := cocone
        isColimit := { desc := desc, fac := laws.1, uniq := laws.2 } }

end AlgebraicGeometry.AlgebraicSpace
