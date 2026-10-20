module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData

/-!
# Descent data and coproducts of algebraic spaces

Taking coproducts identifies descent data for a small family with descent data for its
induced coproduct morphism. Restriction along the coproduct injections is the inverse.
-/

-- Public constructions retain their explicit bodies while their implementation facts stay private.
set_option backward.privateInPublic true

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite AlgebraicGeometry.AlgebraicSpace.ReasLibPullback

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.DescentData

variable {I : Type v} [Small.{u} I] {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X)

/-- The coproduct of a small family of algebraic spaces, regarded as a family indexed by
`PUnit`. -/
abbrev coproductFamily : PUnit.{v + 1} → AlgebraicSpace S :=
  fun _ ↦ coproduct Xᵢ

/-- The singleton family whose sole map is the coproduct of the original maps `f i`. -/
abbrev coproductArrow : ∀ p : PUnit.{v + 1}, coproductFamily Xᵢ p ⟶ X :=
  fun _ ↦ coproductDesc f

/-- Each coproduct inclusion triangles with `coproductArrow` to recover the original map. -/
theorem coproductInjection_fac (i : I) :
    coproductι Xᵢ i ≫ coproductArrow Xᵢ f PUnit.unit = f i ≫ 𝟙 X := sorry

/-- Restriction along all coproduct inclusions, from descent data for the coproduct morphism to
descent data for the original family. -/
noncomputable def restrictCoproduct :
    DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f) ⥤ DescentData Xᵢ f :=
  Pseudofunctor.DescentData.pullFunctor (overPseudofunctor S) (coproductInjection_fac Xᵢ f)

/-- The object over `coproduct Xᵢ` obtained by taking the coproduct of the component objects of a
descent datum. -/
noncomputable def assembledObject (D : DescentData Xᵢ f) : Over (coproduct Xᵢ) :=
  Over.mk (coproductDesc fun i ↦ (D.obj i).hom ≫ coproductι Xᵢ i)

/-- The coproduct of the underlying component maps of a morphism of descent data. -/
noncomputable def assembledMapLeft {D E : DescentData Xᵢ f} (ψ : D ⟶ E) :
    coproduct (fun i ↦ (D.obj i).left) ⟶ coproduct (fun i ↦ (E.obj i).left) :=
  coproductDesc fun i ↦ (ψ.hom i).left ≫ coproductι (fun j ↦ (E.obj j).left) i

/-- The componentwise coproduct map respects the structure maps of assembled objects. -/
private theorem assembledObjectMap_fac {D E : DescentData Xᵢ f} (ψ : D ⟶ E) :
    assembledMapLeft Xᵢ f ψ ≫ (assembledObject Xᵢ f E).hom =
      (assembledObject Xᵢ f D).hom := sorry

/-- A componentwise morphism of descent data induces a morphism between their assembled objects
over `coproduct Xᵢ`. -/
noncomputable def assembledObjectMap {D E : DescentData Xᵢ f} (ψ : D ⟶ E) :
    assembledObject Xᵢ f D ⟶ assembledObject Xᵢ f E :=
  Over.homMk (assembledMapLeft Xᵢ f ψ) (assembledObjectMap_fac Xᵢ f ψ)

/-- The assembled object map induced by an identity morphism is the identity. -/
theorem assembledObjectMap_id (D : DescentData Xᵢ f) :
    assembledObjectMap Xᵢ f (𝟙 D) = 𝟙 (assembledObject Xᵢ f D) := sorry

/-- Assembled object maps preserve composition. -/
theorem assembledObjectMap_comp {D E F : DescentData Xᵢ f} (ψ : D ⟶ E) (χ : E ⟶ F) :
    assembledObjectMap Xᵢ f (ψ ≫ χ) =
      assembledObjectMap Xᵢ f ψ ≫ assembledObjectMap Xᵢ f χ := sorry

/-- Structure-map triangle for a summand of an assembled object. -/
private theorem assembledι_fac (D : DescentData Xᵢ f) (i : I) :
    coproductι (fun j ↦ (D.obj j).left) i ≫ (assembledObject Xᵢ f D).hom =
      (D.obj i).hom ≫ coproductι Xᵢ i := sorry

/-- The first projection of the fibre product of `Vⱼ` with `Z` along `a`. -/
private noncomputable def summandPullbackFst (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (a : Z ⟶ coproduct Xᵢ) (j : I) :
    pullbackOver ((D.obj j).hom ≫ coproductι Xᵢ j) a
        (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal ⟶
      (D.obj j).left :=
  pullbackOverFst ((D.obj j).hom ≫ coproductι Xᵢ j) a
    (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal

/-- The second projection of the fibre product of `Vⱼ` with `Z` along `a`. -/
private noncomputable def summandPullbackSnd (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (a : Z ⟶ coproduct Xᵢ) (j : I) :
    pullbackOver ((D.obj j).hom ≫ coproductι Xᵢ j) a
        (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal ⟶ Z :=
  pullbackOverSnd ((D.obj j).hom ≫ coproductι Xᵢ j) a
    (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal

/-- The comparison of `W = Z ×_Y Vⱼ` with `Xₖ` along the map `W ⟶ Y` induced by `b`. -/
abbrev assembledHomLocalObj (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (a b : Z ⟶ coproduct Xᵢ) (j k : I) : AlgebraicSpace S :=
  pullbackSummands (coproductι Xᵢ) (summandPullbackSnd Xᵢ f D a j ≫ b) k

/-- The map from a local overlap piece to `Xₖ`. -/
private noncomputable def assembledHomLocalToXₖ (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (a b : Z ⟶ coproduct Xᵢ) (j k : I) :
    assembledHomLocalObj Xᵢ f D a b j k ⟶ Xᵢ k :=
  pullbackOverFst (coproductι Xᵢ k) (summandPullbackSnd Xᵢ f D a j ≫ b)
    (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal

/-- The map from a local overlap piece to `W = Z ×_Y Vⱼ`. -/
noncomputable def assembledHomLocalToW (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (a b : Z ⟶ coproduct Xᵢ) (j k : I) :
    assembledHomLocalObj Xᵢ f D a b j k ⟶
      pullbackOver ((D.obj j).hom ≫ coproductι Xᵢ j) a
        (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal :=
  pullbackOverSnd (coproductι Xᵢ k) (summandPullbackSnd Xᵢ f D a j ≫ b)
    (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal

/-- The map from a local overlap piece to `Xⱼ`. -/
private noncomputable def assembledHomLocalToXⱼ (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (a b : Z ⟶ coproduct Xᵢ) (j k : I) :
    assembledHomLocalObj Xᵢ f D a b j k ⟶ Xᵢ j :=
  assembledHomLocalToW Xᵢ f D a b j k ≫ summandPullbackFst Xᵢ f D a j ≫ (D.obj j).hom

/-- The two maps from a local overlap piece to `X` agree. -/
private theorem assembledHomLocal_source_fac (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) (j k : I) :
    assembledHomLocalToXⱼ Xᵢ f D a b j k ≫ f j =
      assembledHomLocalToXₖ Xᵢ f D a b j k ≫ f k := sorry

/-- The cone identity lifting a local overlap piece into the slice pullback of `Vⱼ`. -/
private theorem assembledHomLocalSourceLift_fac (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (a b : Z ⟶ coproduct Xᵢ) (j k : I) :
    assembledHomLocalToW Xᵢ f D a b j k ≫ summandPullbackFst Xᵢ f D a j ≫
        (D.obj j).hom =
      𝟙 (assembledHomLocalObj Xᵢ f D a b j k) ≫ assembledHomLocalToXⱼ Xᵢ f D a b j k := sorry

/-- The lift of a local overlap piece into the slice pullback of `Vⱼ` along the map to `Xⱼ`. -/
private noncomputable def assembledHomLocalSourceLift (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (a b : Z ⟶ coproduct Xᵢ) (j k : I) :
    assembledHomLocalObj Xᵢ f D a b j k ⟶
      ((overPullback (assembledHomLocalToXⱼ Xᵢ f D a b j k)).obj (D.obj j)).left :=
  pullbackLift (D.obj j).hom (assembledHomLocalToXⱼ Xᵢ f D a b j k)
    (assembledHomLocalToW Xᵢ f D a b j k ≫ summandPullbackFst Xᵢ f D a j)
    (𝟙 _)
    (assembledHomLocalSourceLift_fac Xᵢ f D a b j k)

/-- On a local overlap piece, apply the original pairwise descent comparison and project to
`Vₖ`. -/
private noncomputable def assembledHomLocal (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) (j k : I) :
    assembledHomLocalObj Xᵢ f D a b j k ⟶ (D.obj k).left :=
  assembledHomLocalSourceLift Xᵢ f D a b j k ≫
    (D.hom (assembledHomLocalToXₖ Xᵢ f D a b j k ≫ f k)
        (assembledHomLocalToXⱼ Xᵢ f D a b j k)
        (assembledHomLocalToXₖ Xᵢ f D a b j k)
        (assembledHomLocal_source_fac Xᵢ f D q a b ha hb j k) rfl).left ≫
    overPullbackFst (assembledHomLocalToXₖ Xᵢ f D a b j k) (D.obj k)

/-- The coproduct of the inclusions is the identity on the coproduct. -/
private theorem coproductDesc_ι (G : I → AlgebraicSpace S) :
    coproductDesc (coproductι G) = 𝟙 (coproduct G) := sorry

/-- The identity cone relating `snd ≫ b` to the coproduct of the inclusions. -/
private theorem assembledHomSummandIdPullback_fac (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (a b : Z ⟶ coproduct Xᵢ) (j : I) :
    (summandPullbackSnd Xᵢ f D a j ≫ b) ≫ coproductDesc (coproductι Xᵢ) =
      𝟙 _ ≫ (summandPullbackSnd Xᵢ f D a j ≫ b) := sorry

/-- The identity-pullback of `W` along the map to the coproduct induced by `b`. -/
private noncomputable def assembledHomSummandIdPullback (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (a b : Z ⟶ coproduct Xᵢ) (j : I) :
    pullbackOver ((D.obj j).hom ≫ coproductι Xᵢ j) a
        (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal ⟶
      pullbackOver (coproductDesc (coproductι Xᵢ)) (summandPullbackSnd Xᵢ f D a j ≫ b)
        (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal :=
  pullbackLift (coproductDesc (coproductι Xᵢ)) (summandPullbackSnd Xᵢ f D a j ≫ b)
    (summandPullbackSnd Xᵢ f D a j ≫ b) (𝟙 _)
    (assembledHomSummandIdPullback_fac Xᵢ f D a b j)

/-- From a summand fibre product, the twisted map to the coproduct of the component spaces. -/
private noncomputable def assembledHomSummandToV (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) (j : I) :
    pullbackOver ((D.obj j).hom ≫ coproductι Xᵢ j) a
        (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal ⟶
      (assembledObject Xᵢ f D).left :=
  assembledHomSummandIdPullback Xᵢ f D a b j ≫
    pullbackCoproductInv (coproductι Xᵢ) (summandPullbackSnd Xᵢ f D a j ≫ b) ≫
      coproductDesc fun k ↦
        assembledHomLocal Xᵢ f D q a b ha hb j k ≫
          coproductι (fun i ↦ (D.obj i).left) k

/-- The twisted map to the assembled object lies over `b`. -/
private theorem assembledHomSummand_fac (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) (j : I) :
    assembledHomSummandToV Xᵢ f D q a b ha hb j ≫ (assembledObject Xᵢ f D).hom =
      summandPullbackSnd Xᵢ f D a j ≫ b := sorry

/-- The comparison from a summand fibre product of the assembled source to the fibre product
along `b`. -/
private noncomputable def assembledHomSummand (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) (j : I) :
    pullbackOver ((D.obj j).hom ≫ coproductι Xᵢ j) a
        (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal ⟶
      pullbackOver (assembledObject Xᵢ f D).hom b
        (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal :=
  pullbackLift (assembledObject Xᵢ f D).hom b
    (assembledHomSummandToV Xᵢ f D q a b ha hb j)
    (summandPullbackSnd Xᵢ f D a j)
    (assembledHomSummand_fac Xᵢ f D q a b ha hb j)

/-- The underlying assembled comparison morphism, obtained by transporting the original pairwise
comparisons along the pullback-coproduct identification. -/
noncomputable def assembledHomLeft (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) :
    ((overPullback a).obj (assembledObject Xᵢ f D)).left ⟶
      ((overPullback b).obj (assembledObject Xᵢ f D)).left :=
  pullbackCoproductInv (fun j ↦ (D.obj j).hom ≫ coproductι Xᵢ j) a ≫
    coproductDesc (fun j ↦ assembledHomSummand Xᵢ f D q a b ha hb j)

/-- The assembled comparison morphism is a morphism over the common test algebraic space. -/
private theorem assembledHomLeft_fac (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) :
    assembledHomLeft Xᵢ f D q a b ha hb ≫ overPullbackSnd b (assembledObject Xᵢ f D) =
      overPullbackSnd a (assembledObject Xᵢ f D) := sorry

/-- The descent comparison between two pullbacks of an assembled object. -/
noncomputable def assembledHom (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) :
    ((overPseudofunctor S).map a.op.toLoc).toFunctor.obj (assembledObject Xᵢ f D) ⟶
      ((overPseudofunctor S).map b.op.toLoc).toFunctor.obj (assembledObject Xᵢ f D) :=
  Over.homMk (assembledHomLeft Xᵢ f D q a b ha hb)
    (assembledHomLeft_fac Xᵢ f D q a b ha hb)

/-- The assembled comparison maps commute with further pullback. -/
private theorem assembledHom_pull_source_fac {Z' Z : AlgebraicSpace S}
    (g : Z' ⟶ Z) (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : g ≫ q = q')
    (a : Z ⟶ coproduct Xᵢ) (ha : a ≫ coproductDesc f = q)
    (ga : Z' ⟶ coproduct Xᵢ) (hga : g ≫ a = ga) :
    ga ≫ coproductDesc f = q' := sorry

/-- The assembled comparison maps commute with further pullback. -/
private theorem assembledHom_pull (D : DescentData Xᵢ f) {Z' Z : AlgebraicSpace S}
    (g : Z' ⟶ Z) (q : Z ⟶ X) (q' : Z' ⟶ X) (hq : g ≫ q = q')
    (a b : Z ⟶ coproduct Xᵢ) (ha : a ≫ coproductDesc f = q)
    (hb : b ≫ coproductDesc f = q) (ga gb : Z' ⟶ coproduct Xᵢ)
    (hga : g ≫ a = ga) (hgb : g ≫ b = gb) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := overPseudofunctor S)
        (assembledHom Xᵢ f D q a b ha hb) g ga gb =
      assembledHom Xᵢ f D q' ga gb
        (assembledHom_pull_source_fac Xᵢ f g q q' hq a ha ga hga)
        (assembledHom_pull_source_fac Xᵢ f g q q' hq b hb gb hgb) := sorry

/-- The assembled comparison for two equal component maps is the identity. -/
private theorem assembledHom_self (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a : Z ⟶ coproduct Xᵢ) (ha : a ≫ coproductDesc f = q) :
    assembledHom Xᵢ f D q a a ha ha = 𝟙 _ := sorry

/-- The assembled comparison maps satisfy the cocycle law. -/
private theorem assembledHom_comp (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b c : Z ⟶ coproduct Xᵢ) (ha : a ≫ coproductDesc f = q)
    (hb : b ≫ coproductDesc f = q) (hc : c ≫ coproductDesc f = q) :
    assembledHom Xᵢ f D q a b ha hb ≫ assembledHom Xᵢ f D q b c hb hc =
      assembledHom Xᵢ f D q a c ha hc := sorry

/-- Assemble a family-indexed descent datum by taking the coproduct of its component objects and
the coproduct of the pairwise comparison morphisms. -/
noncomputable def assembleCoproductObj (D : DescentData Xᵢ f) :
    DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f) where
  obj _ := assembledObject Xᵢ f D
  hom _ q _ _ a b ha hb := assembledHom Xᵢ f D q a b ha hb
  pullHom_hom _ _ g q q' hq _ _ a b ha hb ga gb hga hgb :=
    assembledHom_pull Xᵢ f D g q q' hq a b ha hb ga gb hga hgb
  hom_self _ q _ a ha := assembledHom_self Xᵢ f D q a ha
  hom_comp _ q _ _ _ a b c ha hb hc := assembledHom_comp Xᵢ f D q a b c ha hb hc

/-- Componentwise coproduct maps commute with the assembled descent comparisons. -/
private theorem assembledHom_naturality {D E : DescentData Xᵢ f} (ψ : D ⟶ E)
    {Z : AlgebraicSpace S} (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) :
    ((overPseudofunctor S).map a.op.toLoc).toFunctor.map (assembledObjectMap Xᵢ f ψ) ≫
        assembledHom Xᵢ f E q a b ha hb =
      assembledHom Xᵢ f D q a b ha hb ≫
        ((overPseudofunctor S).map b.op.toLoc).toFunctor.map (assembledObjectMap Xᵢ f ψ) :=
  sorry

/-- Assemble a morphism of family-indexed descent data componentwise on coproducts. -/
noncomputable def assembleCoproductMap {D E : DescentData Xᵢ f} (ψ : D ⟶ E) :
    assembleCoproductObj Xᵢ f D ⟶ assembleCoproductObj Xᵢ f E where
  hom _ := assembledObjectMap Xᵢ f ψ
  comm _ q _ _ a b ha hb := assembledHom_naturality Xᵢ f ψ q a b ha hb

/-- Assembly carries an identity morphism to an identity morphism. -/
private theorem assembleCoproductMap_id (D : DescentData Xᵢ f) :
    assembleCoproductMap Xᵢ f (𝟙 D) = 𝟙 (assembleCoproductObj Xᵢ f D) := sorry

/-- Assembly carries composition to composition. -/
private theorem assembleCoproductMap_comp {D E F : DescentData Xᵢ f} (ψ : D ⟶ E) (χ : E ⟶ F) :
    assembleCoproductMap Xᵢ f (ψ ≫ χ) =
      assembleCoproductMap Xᵢ f ψ ≫ assembleCoproductMap Xᵢ f χ := sorry

/-- Assemble family-indexed descent data into descent data for the coproduct morphism by taking
coproducts of component objects and morphisms and transporting the overlap comparisons. -/
noncomputable def assembleCoproduct :
    DescentData Xᵢ f ⥤ DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f) where
  obj D := assembleCoproductObj Xᵢ f D
  map ψ := assembleCoproductMap Xᵢ f ψ
  map_id D := assembleCoproductMap_id Xᵢ f D
  map_comp ψ χ := assembleCoproductMap_comp Xᵢ f ψ χ

/-- The sole component of an assembled descent datum is the coproduct of the original component
spaces, mapped to `coproduct Xᵢ` by the coproduct of their structure maps. -/
theorem assembleCoproduct_obj (D : DescentData Xᵢ f) (p : PUnit.{v + 1}) :
    ((assembleCoproduct Xᵢ f).obj D).obj p = assembledObject Xᵢ f D := sorry

/-- On underlying algebraic spaces, assembly sends a morphism to the coproduct of its component
maps. -/
theorem assembleCoproduct_map_left {D E : DescentData Xᵢ f} (ψ : D ⟶ E)
    (p : PUnit.{v + 1}) :
    (((assembleCoproduct Xᵢ f).map ψ).hom p).left = assembledMapLeft Xᵢ f ψ := sorry

/-- The canonical map from one component to the corresponding pullback of the assembled object. -/
private noncomputable def unitComponentLeft (D : DescentData Xᵢ f) (i : I) :
    (D.obj i).left ⟶
      ((overPullback (coproductι Xᵢ i)).obj (assembledObject Xᵢ f D)).left :=
  pullbackLift (assembledObject Xᵢ f D).hom (coproductι Xᵢ i)
    (coproductι (fun j ↦ (D.obj j).left) i) (D.obj i).hom
    (assembledι_fac Xᵢ f D i)

/-- The canonical component map to the restriction of the assembled object lies over `Xᵢ i`. -/
private theorem unitComponentLeft_fac (D : DescentData Xᵢ f) (i : I) :
    unitComponentLeft Xᵢ f D i ≫ overPullbackSnd (coproductι Xᵢ i) (assembledObject Xᵢ f D) =
      (D.obj i).hom := sorry

/-- The canonical component map from a descent datum to the restriction of its assembly. -/
private noncomputable def unitComponentMap (D : DescentData Xᵢ f) (i : I) :
    D.obj i ⟶ ((restrictCoproduct Xᵢ f).obj ((assembleCoproduct Xᵢ f).obj D)).obj i :=
  Over.homMk (unitComponentLeft Xᵢ f D i) (unitComponentLeft_fac Xᵢ f D i)

/-- The canonical component maps commute with every pairwise descent comparison. -/
private theorem unitComponent_comm (D : DescentData Xᵢ f) {Z : AlgebraicSpace S} (q : Z ⟶ X)
    {i j : I} (a : Z ⟶ Xᵢ i) (b : Z ⟶ Xᵢ j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    ((overPseudofunctor S).map a.op.toLoc).toFunctor.map (unitComponentMap Xᵢ f D i) ≫
        (((restrictCoproduct Xᵢ f).obj ((assembleCoproduct Xᵢ f).obj D)).hom q a b ha hb) =
      D.hom q a b ha hb ≫
        ((overPseudofunctor S).map b.op.toLoc).toFunctor.map (unitComponentMap Xᵢ f D j) :=
  sorry

/-- The canonical morphism from a family descent datum to the restriction of its assembled
descent datum. -/
private noncomputable def unitComponent (D : DescentData Xᵢ f) :
    D ⟶ (assembleCoproduct Xᵢ f ⋙ restrictCoproduct Xᵢ f).obj D where
  hom i := unitComponentMap Xᵢ f D i
  comm _ q _ _ a b ha hb := unitComponent_comm Xᵢ f D q a b ha hb

/-- The fibre product of `Vⱼ` with `Xᵢ` over the coproduct. -/
private noncomputable def unitInverseSummandObj (D : DescentData Xᵢ f) (i j : I) : AlgebraicSpace S :=
  pullbackOver ((D.obj j).hom ≫ coproductι Xᵢ j) (coproductι Xᵢ i)
    (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal

/-- The first projection of `unitInverseSummandObj` to `Vⱼ`. -/
private noncomputable def unitInverseSummandFst (D : DescentData Xᵢ f) (i j : I) :
    unitInverseSummandObj Xᵢ f D i j ⟶ (D.obj j).left :=
  pullbackOverFst ((D.obj j).hom ≫ coproductι Xᵢ j) (coproductι Xᵢ i)
    (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal

/-- The second projection of `unitInverseSummandObj` to `Xᵢ`. -/
private noncomputable def unitInverseSummandSnd (D : DescentData Xᵢ f) (i j : I) :
    unitInverseSummandObj Xᵢ f D i j ⟶ Xᵢ i :=
  pullbackOverSnd ((D.obj j).hom ≫ coproductι Xᵢ j) (coproductι Xᵢ i)
    (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal

/-- The map from a unit-inverse summand to `Xⱼ`. -/
private noncomputable def unitInverseSummandToXⱼ (D : DescentData Xᵢ f) (i j : I) :
    unitInverseSummandObj Xᵢ f D i j ⟶ Xᵢ j :=
  unitInverseSummandFst Xᵢ f D i j ≫ (D.obj j).hom

/-- The two maps from a unit-inverse summand to `X` agree. -/
private theorem unitInverseSummand_source_fac (D : DescentData Xᵢ f) (i j : I) :
    unitInverseSummandToXⱼ Xᵢ f D i j ≫ f j =
      unitInverseSummandSnd Xᵢ f D i j ≫ f i := sorry

/-- The cone identity lifting a unit-inverse summand into the slice pullback of `Vⱼ`. -/
private theorem unitInverseSummandSourceLift_fac (D : DescentData Xᵢ f) (i j : I) :
    unitInverseSummandFst Xᵢ f D i j ≫ (D.obj j).hom =
      𝟙 (unitInverseSummandObj Xᵢ f D i j) ≫ unitInverseSummandToXⱼ Xᵢ f D i j := sorry

/-- The lift of a unit-inverse summand into the slice pullback of `Vⱼ`. -/
private noncomputable def unitInverseSummandSourceLift (D : DescentData Xᵢ f) (i j : I) :
    unitInverseSummandObj Xᵢ f D i j ⟶
      ((overPullback (unitInverseSummandToXⱼ Xᵢ f D i j)).obj (D.obj j)).left :=
  pullbackLift (D.obj j).hom (unitInverseSummandToXⱼ Xᵢ f D i j)
    (unitInverseSummandFst Xᵢ f D i j) (𝟙 _)
    (unitInverseSummandSourceLift_fac Xᵢ f D i j)

/-- On a unit-inverse summand, apply the original pairwise descent comparison and project to
`Vᵢ`. -/
private noncomputable def unitInverseSummand (D : DescentData Xᵢ f) (i j : I) :
    unitInverseSummandObj Xᵢ f D i j ⟶ (D.obj i).left :=
  unitInverseSummandSourceLift Xᵢ f D i j ≫
    (D.hom (unitInverseSummandSnd Xᵢ f D i j ≫ f i)
        (unitInverseSummandToXⱼ Xᵢ f D i j)
        (unitInverseSummandSnd Xᵢ f D i j)
        (unitInverseSummand_source_fac Xᵢ f D i j) rfl).left ≫
    overPullbackFst (unitInverseSummandSnd Xᵢ f D i j) (D.obj i)

/-- The explicit inverse of a unit component, obtained by transporting along the
pullback-coproduct identification and applying the original pairwise comparisons. -/
private noncomputable def unitInverseLeft (D : DescentData Xᵢ f) (i : I) :
    ((overPullback (coproductι Xᵢ i)).obj (assembledObject Xᵢ f D)).left ⟶ (D.obj i).left :=
  pullbackCoproductInv (fun j ↦ (D.obj j).hom ≫ coproductι Xᵢ j) (coproductι Xᵢ i) ≫
    coproductDesc fun j ↦ unitInverseSummand Xᵢ f D i j

/-- The underlying inverse to a unit component lies over `Xᵢ i`. -/
private theorem unitInverseLeft_fac (D : DescentData Xᵢ f) (i : I) :
    unitInverseLeft Xᵢ f D i ≫ (D.obj i).hom =
      overPullbackSnd (coproductι Xᵢ i) (assembledObject Xᵢ f D) := sorry

/-- The explicit inverse of the unit component over `Xᵢ i`. -/
private noncomputable def unitInverseMap (D : DescentData Xᵢ f) (i : I) :
    ((restrictCoproduct Xᵢ f).obj ((assembleCoproduct Xᵢ f).obj D)).obj i ⟶ D.obj i :=
  Over.homMk (unitInverseLeft Xᵢ f D i) (unitInverseLeft_fac Xᵢ f D i)

/-- The inverse unit component maps commute with every pairwise descent comparison. -/
private theorem unitInverse_comm (D : DescentData Xᵢ f) {Z : AlgebraicSpace S} (q : Z ⟶ X)
    {i j : I} (a : Z ⟶ Xᵢ i) (b : Z ⟶ Xᵢ j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    ((overPseudofunctor S).map a.op.toLoc).toFunctor.map (unitInverseMap Xᵢ f D i) ≫
        D.hom q a b ha hb =
      (((restrictCoproduct Xᵢ f).obj ((assembleCoproduct Xᵢ f).obj D)).hom q a b ha hb) ≫
        ((overPseudofunctor S).map b.op.toLoc).toFunctor.map (unitInverseMap Xᵢ f D j) :=
  sorry

/-- The explicit inverse of the unit component on family descent data. -/
private noncomputable def unitComponentInv (D : DescentData Xᵢ f) :
    (assembleCoproduct Xᵢ f ⋙ restrictCoproduct Xᵢ f).obj D ⟶ D where
  hom i := unitInverseMap Xᵢ f D i
  comm _ q _ _ a b ha hb := unitInverse_comm Xᵢ f D q a b ha hb

/-- The unit component followed by its explicit inverse is the identity. -/
private theorem unitComponent_hom_inv_id (D : DescentData Xᵢ f) :
    unitComponent Xᵢ f D ≫ unitComponentInv Xᵢ f D = 𝟙 D := sorry

/-- The explicit inverse followed by the unit component is the identity. -/
private theorem unitComponent_inv_hom_id (D : DescentData Xᵢ f) :
    unitComponentInv Xᵢ f D ≫ unitComponent Xᵢ f D =
      𝟙 ((assembleCoproduct Xᵢ f ⋙ restrictCoproduct Xᵢ f).obj D) := sorry

/-- The unit component as an isomorphism with an explicitly constructed inverse. -/
private noncomputable def unitComponentIso (D : DescentData Xᵢ f) :
    D ≅ (assembleCoproduct Xᵢ f ⋙ restrictCoproduct Xᵢ f).obj D where
  hom := unitComponent Xᵢ f D
  inv := unitComponentInv Xᵢ f D
  hom_inv_id := unitComponent_hom_inv_id Xᵢ f D
  inv_hom_id := unitComponent_inv_hom_id Xᵢ f D

/-- The unit components are natural in family-indexed descent data. -/
private theorem unitComponent_naturality {D E : DescentData Xᵢ f} (ψ : D ⟶ E) :
    ψ ≫ unitComponent Xᵢ f E =
      unitComponent Xᵢ f D ≫
        (assembleCoproduct Xᵢ f ⋙ restrictCoproduct Xᵢ f).map ψ := sorry

/-- The canonical unit comparing a family descent datum with the restriction of its assembly. -/
noncomputable def coproductUnitIso :
    𝟭 (DescentData Xᵢ f) ≅ assembleCoproduct Xᵢ f ⋙ restrictCoproduct Xᵢ f :=
  NatIso.ofComponents (unitComponentIso Xᵢ f) (unitComponent_naturality Xᵢ f)

/-- The coproduct of the component pullback projections of a coproduct descent datum. -/
private noncomputable def counitComponentLeft
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    (assembledObject Xᵢ f ((restrictCoproduct Xᵢ f).obj E)).left ⟶ (E.obj PUnit.unit).left :=
  coproductDesc fun i ↦
    overPullbackFst (coproductι Xᵢ i) (E.obj PUnit.unit)

/-- The coproduct of the component pullback projections lies over `coproduct Xᵢ`. -/
private theorem counitComponentLeft_fac
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    counitComponentLeft Xᵢ f E ≫ (E.obj PUnit.unit).hom =
      (assembledObject Xᵢ f ((restrictCoproduct Xᵢ f).obj E)).hom := sorry

/-- The counit component as a morphism of objects over `coproduct Xᵢ`. -/
private noncomputable def counitComponentMap
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    assembledObject Xᵢ f ((restrictCoproduct Xᵢ f).obj E) ⟶ E.obj PUnit.unit :=
  Over.homMk (counitComponentLeft Xᵢ f E) (counitComponentLeft_fac Xᵢ f E)

/-- The counit component maps commute with the assembled descent comparisons. -/
private theorem counitComponent_comm
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f))
    {Z : AlgebraicSpace S} (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) :
    ((overPseudofunctor S).map a.op.toLoc).toFunctor.map (counitComponentMap Xᵢ f E) ≫
        E.hom q a b ha hb =
      assembledHom Xᵢ f ((restrictCoproduct Xᵢ f).obj E) q a b ha hb ≫
        ((overPseudofunctor S).map b.op.toLoc).toFunctor.map (counitComponentMap Xᵢ f E) :=
  sorry

/-- The canonical morphism from the assembly of all restrictions to a descent datum for the
coproduct morphism. -/
private noncomputable def counitComponent
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    (restrictCoproduct Xᵢ f ⋙ assembleCoproduct Xᵢ f).obj E ⟶ E where
  hom _ := counitComponentMap Xᵢ f E
  comm _ q _ _ a b ha hb := counitComponent_comm Xᵢ f E q a b ha hb

/-- The mediating map from the unique component of a coproduct descent datum into the fibre
product along `coproductDesc (coproductι Xᵢ)`. -/
private theorem counitInverseIdPullback_fac
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    (E.obj PUnit.unit).hom ≫ coproductDesc (coproductι Xᵢ) =
      𝟙 (E.obj PUnit.unit).left ≫ (E.obj PUnit.unit).hom := sorry

/-- The mediating map from the unique component of a coproduct descent datum into the fibre
product along the coproduct of the inclusions. -/
private noncomputable def counitInverseIdPullback
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    (E.obj PUnit.unit).left ⟶
      pullbackOver (coproductDesc (coproductι Xᵢ)) (E.obj PUnit.unit).hom
        (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal :=
  pullbackLift (coproductDesc (coproductι Xᵢ)) (E.obj PUnit.unit).hom
    (E.obj PUnit.unit).hom (𝟙 _)
    (counitInverseIdPullback_fac Xᵢ f E)

/-- The explicit inverse of the counit component on coproduct descent data. -/
private noncomputable def counitInverseLeft
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    (E.obj PUnit.unit).left ⟶
      (assembledObject Xᵢ f ((restrictCoproduct Xᵢ f).obj E)).left :=
  counitInverseIdPullback Xᵢ f E ≫
    pullbackCoproductInv (coproductι Xᵢ) (E.obj PUnit.unit).hom ≫
      coproductDesc fun i ↦
        (pullbackSymmetry (C := (Over S)ᵒᵖ ⥤ Type u)
          (coproductι Xᵢ i : (Xᵢ i).functorOfPoints ⟶ (coproduct Xᵢ).functorOfPoints)
          ((E.obj PUnit.unit).hom : (E.obj PUnit.unit).left.functorOfPoints ⟶
            (coproduct Xᵢ).functorOfPoints)).hom ≫
          coproductι
            (fun j ↦ ((overPullback (coproductι Xᵢ j)).obj (E.obj PUnit.unit)).left) i

/-- The explicit inverse of the counit component lies over `coproduct Xᵢ`. -/
private theorem counitInverseLeft_fac
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    counitInverseLeft Xᵢ f E ≫
        (assembledObject Xᵢ f ((restrictCoproduct Xᵢ f).obj E)).hom =
      (E.obj PUnit.unit).hom := sorry

/-- The explicit inverse of the counit component as a morphism over `coproduct Xᵢ`. -/
private noncomputable def counitInverseMap
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    E.obj PUnit.unit ⟶ assembledObject Xᵢ f ((restrictCoproduct Xᵢ f).obj E) :=
  Over.homMk (counitInverseLeft Xᵢ f E) (counitInverseLeft_fac Xᵢ f E)

/-- The inverse counit component maps commute with every pairwise descent comparison. -/
private theorem counitInverse_comm
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f))
    {Z : AlgebraicSpace S} (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) :
    ((overPseudofunctor S).map a.op.toLoc).toFunctor.map (counitInverseMap Xᵢ f E) ≫
        assembledHom Xᵢ f ((restrictCoproduct Xᵢ f).obj E) q a b ha hb =
      E.hom q a b ha hb ≫
        ((overPseudofunctor S).map b.op.toLoc).toFunctor.map (counitInverseMap Xᵢ f E) :=
  sorry

/-- The explicit inverse of the counit component on coproduct descent data. -/
private noncomputable def counitComponentInv
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    E ⟶ (restrictCoproduct Xᵢ f ⋙ assembleCoproduct Xᵢ f).obj E where
  hom _ := counitInverseMap Xᵢ f E
  comm _ q _ _ a b ha hb := counitInverse_comm Xᵢ f E q a b ha hb

/-- The counit component followed by its explicit inverse is the identity. -/
private theorem counitComponent_hom_inv_id
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    counitComponent Xᵢ f E ≫ counitComponentInv Xᵢ f E =
      𝟙 ((restrictCoproduct Xᵢ f ⋙ assembleCoproduct Xᵢ f).obj E) := sorry

/-- The explicit inverse followed by the counit component is the identity. -/
private theorem counitComponent_inv_hom_id
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    counitComponentInv Xᵢ f E ≫ counitComponent Xᵢ f E = 𝟙 E := sorry

/-- The counit component as an isomorphism with an explicitly constructed inverse. -/
private noncomputable def counitComponentIso
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :
    (restrictCoproduct Xᵢ f ⋙ assembleCoproduct Xᵢ f).obj E ≅ E where
  hom := counitComponent Xᵢ f E
  inv := counitComponentInv Xᵢ f E
  hom_inv_id := counitComponent_hom_inv_id Xᵢ f E
  inv_hom_id := counitComponent_inv_hom_id Xᵢ f E

/-- The counit components are natural in descent data for the coproduct morphism. -/
private theorem counitComponent_naturality
    {D E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)} (ψ : D ⟶ E) :
    (restrictCoproduct Xᵢ f ⋙ assembleCoproduct Xᵢ f).map ψ ≫ counitComponent Xᵢ f E =
      counitComponent Xᵢ f D ≫ ψ := sorry

/-- The canonical counit comparing the assembly of all restrictions with a descent datum for the
coproduct morphism. -/
private noncomputable def coproductCounitIso :
    restrictCoproduct Xᵢ f ⋙ assembleCoproduct Xᵢ f ≅
      𝟭 (DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) :=
  NatIso.ofComponents (counitComponentIso Xᵢ f) (counitComponent_naturality Xᵢ f)

/-- The unit and counit satisfy the triangle identity on assembled descent data. -/
private theorem coproductTriangle (D : DescentData Xᵢ f) :
    (assembleCoproduct Xᵢ f).map ((coproductUnitIso Xᵢ f).hom.app D) ≫
        (coproductCounitIso Xᵢ f).hom.app ((assembleCoproduct Xᵢ f).obj D) =
      𝟙 ((assembleCoproduct Xᵢ f).obj D) := sorry

/-- The canonical equivalence between descent data for a family of morphisms of algebraic spaces
and descent data for the induced coproduct morphism. -/
noncomputable def coproductEquivalence :
    DescentData Xᵢ f ≌ DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f) where
  functor := assembleCoproduct Xᵢ f
  inverse := restrictCoproduct Xᵢ f
  unitIso := coproductUnitIso Xᵢ f
  counitIso := coproductCounitIso Xᵢ f
  functor_unitIso_comp D := coproductTriangle Xᵢ f D

/-- Restriction along the coproduct injections is an equivalence of categories. -/
instance instIsEquivalenceRestrictCoproduct : (restrictCoproduct Xᵢ f).IsEquivalence :=
  (coproductEquivalence Xᵢ f).isEquivalence_inverse

/-- Restriction of a coproduct descent datum at `i` is pullback along `coproductι Xᵢ i`. -/
theorem restrictCoproduct_obj
    (E : DescentData (coproductFamily Xᵢ) (coproductArrow Xᵢ f)) (i : I) :
    ((restrictCoproduct Xᵢ f).obj E).obj i =
      (overPullback (coproductι Xᵢ i)).obj (E.obj PUnit.unit) := sorry

/-- Under `coproductEquivalence`, the sole component object is the coproduct of the component
spaces, with its induced map to `coproduct Xᵢ`. -/
theorem coproductEquivalence_obj (D : DescentData Xᵢ f) (p : PUnit.{v + 1}) :
    ((coproductEquivalence Xᵢ f).functor.obj D).obj p =
      Over.mk (coproductDesc fun i ↦ (D.obj i).hom ≫ coproductι Xᵢ i) := sorry

/-- The map assembled by `coproductEquivalence` is characterized on every coproduct injection by
the corresponding component map. -/
theorem coproductEquivalence_map_ι {D E : DescentData Xᵢ f} (ψ : D ⟶ E) (i : I) :
    coproductι (fun j ↦ (D.obj j).left) i ≫
        ((((coproductEquivalence Xᵢ f).functor.map ψ).hom PUnit.unit).left) =
      (ψ.hom i).left ≫ coproductι (fun j ↦ (E.obj j).left) i := sorry

/-- The `j`-th pullback-coproduct inclusion into the fibre product of an assembled object
along a map `a` to `coproduct Xᵢ`. -/
noncomputable def assembledHomSourceι (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (a : Z ⟶ coproduct Xᵢ) (j : I) :
    pullbackOver ((D.obj j).hom ≫ coproductι Xᵢ j) a
        (coproduct Xᵢ).isSheaf (coproduct Xᵢ).representableDiagonal ⟶
      ((overPullback a).obj (assembledObject Xᵢ f D)).left :=
  coproductι (pullbackSummands (fun i ↦ (D.obj i).hom ≫ coproductι Xᵢ i) a) j ≫
    pullbackCoproductHom (fun i ↦ (D.obj i).hom ≫ coproductι Xᵢ i) a

/-- The local overlap comparison into the assembled object lies over `b`. -/
private theorem assembledHomLocalLift_fac (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) (j k : I) :
    (assembledHomLocal Xᵢ f D q a b ha hb j k ≫
        coproductι (fun i ↦ (D.obj i).left) k) ≫ (assembledObject Xᵢ f D).hom =
      (assembledHomLocalToW Xᵢ f D a b j k ≫ summandPullbackSnd Xᵢ f D a j) ≫ b := sorry

/-- The original pairwise descent comparison `D.hom`, transported through the canonical overlap
pullbacks and included into the fibre product of the assembled object along `b`. -/
noncomputable def assembledHomLocalLift (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) (j k : I) :
    assembledHomLocalObj Xᵢ f D a b j k ⟶
      ((overPullback b).obj (assembledObject Xᵢ f D)).left :=
  pullbackLift (assembledObject Xᵢ f D).hom b
    (assembledHomLocal Xᵢ f D q a b ha hb j k ≫
      coproductι (fun i ↦ (D.obj i).left) k)
    (assembledHomLocalToW Xᵢ f D a b j k ≫ summandPullbackSnd Xᵢ f D a j)
    (assembledHomLocalLift_fac Xᵢ f D q a b ha hb j k)

/-- Restricting the assembled comparison along the `j`-th then `k`-th pullback-coproduct
inclusions recovers the original pairwise descent comparison `D.hom`, transported through
the canonical overlap pullbacks. -/
theorem coproductEquivalence_hom_ι (D : DescentData Xᵢ f) {Z : AlgebraicSpace S}
    (q : Z ⟶ X) (a b : Z ⟶ coproduct Xᵢ)
    (ha : a ≫ coproductDesc f = q) (hb : b ≫ coproductDesc f = q) (j k : I) :
    assembledHomLocalToW Xᵢ f D a b j k ≫
        assembledHomSourceι Xᵢ f D a j ≫
          ((((coproductEquivalence Xᵢ f).functor.obj D).hom
            (i₁ := PUnit.unit) (i₂ := PUnit.unit) q a b ha hb).left) =
      assembledHomLocalLift Xᵢ f D q a b ha hb j k := sorry

end AlgebraicGeometry.AlgebraicSpace.DescentData
