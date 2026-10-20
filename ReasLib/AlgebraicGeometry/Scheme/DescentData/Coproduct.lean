module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.DescentData

/-!
# Descent data and coproduct morphisms

This module compares descent data for a small family of scheme morphisms with descent data for
the morphism from the coproduct of their sources.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme.DescentData

variable {I : Type v} [Small.{u} I] {S : Scheme.{u}}
variable (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ S)

/-- The coproduct family regarded as a family indexed by `PUnit`. -/
abbrev coproductFamily : PUnit.{1} → Scheme.{u} :=
  fun _ ↦ ∐ X

/-- The family indexed by `PUnit` whose sole map is `Sigma.desc f`. -/
abbrev coproductArrow : ∀ p : PUnit.{1}, coproductFamily X p ⟶ S :=
  fun _ ↦ Sigma.desc f

/-- The coproduct injection triangles used to restrict descent data along the family. -/
theorem coproductInjection_fac (i : I) :
    Sigma.ι X i ≫ coproductArrow X f PUnit.unit = f i ≫ 𝟙 S := sorry

/-- Restriction along all coproduct injections, from descent data for `Sigma.desc f` to descent
data for the original family. -/
noncomputable def restrictCoproduct :
    DescentData (coproductFamily X) (coproductArrow X f) ⥤ DescentData X f :=
  Pseudofunctor.DescentData.pullFunctor overPseudofunctor
    (coproductInjection_fac X f)

/-- The object over `∐ X` obtained by taking the coproduct of the component objects of a descent
datum. -/
noncomputable def assembledObject (D : DescentData X f) : Over (∐ X) :=
  Over.mk (Sigma.desc fun i ↦ (D.obj i).hom ≫ Sigma.ι X i)

/-- The coproduct of the underlying component maps of a morphism of descent data. -/
noncomputable def assembledMapLeft {D E : DescentData X f} (ψ : D ⟶ E) :
    (∐ fun i ↦ (D.obj i).left) ⟶ ∐ fun i ↦ (E.obj i).left :=
  CategoryTheory.Limits.Sigma.map fun i ↦ (ψ.hom i).left

/-- The componentwise coproduct map respects the structure maps of assembled objects. -/
theorem assembledObjectMap_fac {D E : DescentData X f} (ψ : D ⟶ E) :
    assembledMapLeft X f ψ ≫ (assembledObject X f E).hom =
      (assembledObject X f D).hom := sorry

/-- A componentwise morphism of descent data induces a morphism between their assembled objects
over `∐ X`. -/
noncomputable def assembledObjectMap {D E : DescentData X f} (ψ : D ⟶ E) :
    assembledObject X f D ⟶ assembledObject X f E :=
  Over.homMk (assembledMapLeft X f ψ) (assembledObjectMap_fac X f ψ)

/-- The assembled object map induced by an identity morphism is the identity. -/
theorem assembledObjectMap_id (D : DescentData X f) :
    assembledObjectMap X f (𝟙 D) = 𝟙 (assembledObject X f D) := sorry

/-- Assembled object maps preserve composition. -/
theorem assembledObjectMap_comp {D E F : DescentData X f} (ψ : D ⟶ E) (χ : E ⟶ F) :
    assembledObjectMap X f (ψ ≫ χ) =
      assembledObjectMap X f ψ ≫ assembledObjectMap X f χ := sorry

/-- The cover used to define the assembled comparison map: first select a component of the
assembled source object, then a component of the target coproduct. -/
noncomputable def assembledHomCover (D : DescentData X f) {Y : Scheme.{u}}
    (a b : Y ⟶ ∐ X) :
    Scheme.OpenCover (pullback (assembledObject X f D).hom a) :=
  let sourceCover :=
    (AlgebraicGeometry.sigmaOpenCover (fun i ↦ (D.obj i).left)).pullback₁
      (pullback.fst (assembledObject X f D).hom a)
  sourceCover.bind fun i ↦
    (AlgebraicGeometry.sigmaOpenCover X).pullback₁
      (sourceCover.f i ≫ pullback.snd (assembledObject X f D).hom a ≫ b)

/-- The map from a member of `assembledHomCover` to its selected source component. -/
noncomputable def assembledHomCoverToSourceComponent (D : DescentData X f)
    {Y : Scheme.{u}} (a b : Y ⟶ ∐ X) (ij : (assembledHomCover X f D a b).I₀) :
    (assembledHomCover X f D a b).X ij ⟶ (D.obj ij.1).left :=
  let componentCover := AlgebraicGeometry.sigmaOpenCover (fun i ↦ (D.obj i).left)
  let sourceCover :=
    componentCover.pullback₁
      (pullback.fst (assembledObject X f D).hom a)
  let targetCover :=
    (AlgebraicGeometry.sigmaOpenCover X).pullback₁
      (sourceCover.f ij.1 ≫ pullback.snd (assembledObject X f D).hom a ≫ b)
  targetCover.f ij.2 ≫ AlgebraicGeometry.Scheme.Cover.pullbackHom componentCover
    (pullback.fst (assembledObject X f D).hom a) ij.1

/-- The map from a member of `assembledHomCover` to the selected target component `X j`. -/
noncomputable def assembledHomCoverToTargetBase (D : DescentData X f)
    {Y : Scheme.{u}} (a b : Y ⟶ ∐ X) (ij : (assembledHomCover X f D a b).I₀) :
    (assembledHomCover X f D a b).X ij ⟶ X ij.2 :=
  let sourceCover :=
    (AlgebraicGeometry.sigmaOpenCover (fun i ↦ (D.obj i).left)).pullback₁
      (pullback.fst (assembledObject X f D).hom a)
  let componentCover := AlgebraicGeometry.sigmaOpenCover X
  let targetCover :=
    componentCover.pullback₁
      (sourceCover.f ij.1 ≫ pullback.snd (assembledObject X f D).hom a ≫ b)
  (AlgebraicGeometry.Scheme.Cover.pullbackHom componentCover
    (sourceCover.f ij.1 ≫ pullback.snd (assembledObject X f D).hom a ≫ b) ij.2 :
      targetCover.X ij.2 ⟶ X ij.2)

/-- The map from a member of `assembledHomCover` to the common test scheme. -/
noncomputable def assembledHomCoverToBase (D : DescentData X f)
    {Y : Scheme.{u}} (a b : Y ⟶ ∐ X) (ij : (assembledHomCover X f D a b).I₀) :
    (assembledHomCover X f D a b).X ij ⟶ Y :=
  (assembledHomCover X f D a b).f ij ≫
    pullback.snd (assembledObject X f D).hom a

/-- The selected source-component map lies over the map to `X i`. -/
theorem assembledHomCover_source_fac (D : DescentData X f) {Y : Scheme.{u}}
    (a b : Y ⟶ ∐ X) (ij : (assembledHomCover X f D a b).I₀) :
    assembledHomCoverToSourceComponent X f D a b ij ≫ (D.obj ij.1).hom ≫
        Sigma.ι X ij.1 = assembledHomCoverToBase X f D a b ij ≫ a := sorry

/-- The selected target-base map is the component of the map to the target coproduct. -/
theorem assembledHomCover_target_fac (D : DescentData X f) {Y : Scheme.{u}}
    (a b : Y ⟶ ∐ X) (ij : (assembledHomCover X f D a b).I₀) :
    assembledHomCoverToTargetBase X f D a b ij ≫ Sigma.ι X ij.2 =
      assembledHomCoverToBase X f D a b ij ≫ b := sorry

/-- The selected source-component map, viewed as a map to `X i`. -/
noncomputable def assembledHomCoverToSourceBase (D : DescentData X f)
    {Y : Scheme.{u}} (a b : Y ⟶ ∐ X) (ij : (assembledHomCover X f D a b).I₀) :
    (assembledHomCover X f D a b).X ij ⟶ X ij.1 :=
  assembledHomCoverToSourceComponent X f D a b ij ≫ (D.obj ij.1).hom

/-- Both selected component maps lie over the same map to `S`, on the source side. -/
theorem assembledHomCoverToSourceBase_fac (D : DescentData X f)
    {Y : Scheme.{u}} (q : Y ⟶ S) (a b : Y ⟶ ∐ X)
    (ha : a ≫ Sigma.desc f = q) (ij : (assembledHomCover X f D a b).I₀) :
    assembledHomCoverToSourceBase X f D a b ij ≫ f ij.1 =
      assembledHomCoverToBase X f D a b ij ≫ q := sorry

/-- Both selected component maps lie over the same map to `S`, on the target side. -/
theorem assembledHomCoverToTargetBase_fac (D : DescentData X f)
    {Y : Scheme.{u}} (q : Y ⟶ S) (a b : Y ⟶ ∐ X)
    (hb : b ≫ Sigma.desc f = q) (ij : (assembledHomCover X f D a b).I₀) :
    assembledHomCoverToTargetBase X f D a b ij ≫ f ij.2 =
      assembledHomCoverToBase X f D a b ij ≫ q := sorry

/-- The canonical section from a member of `assembledHomCover` to the pullback of its selected
source component. -/
noncomputable def assembledHomLocalSourceLift (D : DescentData X f)
    {Y : Scheme.{u}} (a b : Y ⟶ ∐ X) (ij : (assembledHomCover X f D a b).I₀) :
    (assembledHomCover X f D a b).X ij ⟶
      pullback (D.obj ij.1).hom (assembledHomCoverToSourceBase X f D a b ij) :=
  pullback.lift (assembledHomCoverToSourceComponent X f D a b ij) (𝟙 _)
    (Category.id_comp _).symm

/-- On a member of `assembledHomCover`, apply the original pairwise descent comparison and
project to the selected target component. -/
noncomputable def assembledHomLocalToTargetComponent (D : DescentData X f)
    {Y : Scheme.{u}} (q : Y ⟶ S) (a b : Y ⟶ ∐ X)
    (ha : a ≫ Sigma.desc f = q) (hb : b ≫ Sigma.desc f = q)
    (ij : (assembledHomCover X f D a b).I₀) :
    (assembledHomCover X f D a b).X ij ⟶ (D.obj ij.2).left :=
  assembledHomLocalSourceLift X f D a b ij ≫
    (D.hom (assembledHomCoverToBase X f D a b ij ≫ q)
      (assembledHomCoverToSourceBase X f D a b ij)
      (assembledHomCoverToTargetBase X f D a b ij)
      (assembledHomCoverToSourceBase_fac X f D q a b ha ij)
      (assembledHomCoverToTargetBase_fac X f D q a b hb ij)).left ≫
    pullback.fst (D.obj ij.2).hom (assembledHomCoverToTargetBase X f D a b ij)

/-- The local comparison lands over the target map to the coproduct. -/
theorem assembledHomLocalToTargetComponent_fac (D : DescentData X f)
    {Y : Scheme.{u}} (q : Y ⟶ S) (a b : Y ⟶ ∐ X)
    (ha : a ≫ Sigma.desc f = q) (hb : b ≫ Sigma.desc f = q)
    (ij : (assembledHomCover X f D a b).I₀) :
    assembledHomLocalToTargetComponent X f D q a b ha hb ij ≫
        Sigma.ι (fun i ↦ (D.obj i).left) ij.2 ≫ (assembledObject X f D).hom =
      assembledHomCoverToBase X f D a b ij ≫ b := sorry

/-- The local comparison map between the two pullbacks of the assembled object. -/
noncomputable def assembledHomLocal (D : DescentData X f)
    {Y : Scheme.{u}} (q : Y ⟶ S) (a b : Y ⟶ ∐ X)
    (ha : a ≫ Sigma.desc f = q) (hb : b ≫ Sigma.desc f = q)
    (ij : (assembledHomCover X f D a b).I₀) :
    (assembledHomCover X f D a b).X ij ⟶ pullback (assembledObject X f D).hom b :=
  pullback.lift
    (assembledHomLocalToTargetComponent X f D q a b ha hb ij ≫
      Sigma.ι (fun i ↦ (D.obj i).left) ij.2)
    (assembledHomCoverToBase X f D a b ij)
    (assembledHomLocalToTargetComponent_fac X f D q a b ha hb ij)

/-- The local comparison maps agree on overlaps of `assembledHomCover`. -/
theorem assembledHomLocal_compat (D : DescentData X f)
    {Y : Scheme.{u}} (q : Y ⟶ S) (a b : Y ⟶ ∐ X)
    (ha : a ≫ Sigma.desc f = q) (hb : b ≫ Sigma.desc f = q) :
    ∀ ij kl,
      pullback.fst ((assembledHomCover X f D a b).f ij)
          ((assembledHomCover X f D a b).f kl) ≫
        assembledHomLocal X f D q a b ha hb ij =
      pullback.snd ((assembledHomCover X f D a b).f ij)
          ((assembledHomCover X f D a b).f kl) ≫
        assembledHomLocal X f D q a b ha hb kl := sorry

/-- The underlying assembled comparison morphism, obtained by gluing the original pairwise
comparison maps over all pairs of coproduct components. -/
noncomputable def assembledHomLeft (D : DescentData X f)
    {Y : Scheme.{u}} (q : Y ⟶ S) (a b : Y ⟶ ∐ X)
    (ha : a ≫ Sigma.desc f = q) (hb : b ≫ Sigma.desc f = q) :
    pullback (assembledObject X f D).hom a ⟶ pullback (assembledObject X f D).hom b :=
  AlgebraicGeometry.Scheme.Cover.glueMorphisms (assembledHomCover X f D a b)
    (assembledHomLocal X f D q a b ha hb)
    (assembledHomLocal_compat X f D q a b ha hb)

/-- The assembled comparison morphism is a morphism over the common test scheme. -/
theorem assembledHomLeft_fac (D : DescentData X f)
    {Y : Scheme.{u}} (q : Y ⟶ S) (a b : Y ⟶ ∐ X)
    (ha : a ≫ Sigma.desc f = q) (hb : b ≫ Sigma.desc f = q) :
    assembledHomLeft X f D q a b ha hb ≫ pullback.snd (assembledObject X f D).hom b =
      pullback.snd (assembledObject X f D).hom a := sorry

/-- The descent comparison between two pullbacks of an assembled object. -/
noncomputable def assembledHom (D : DescentData X f)
    {Y : Scheme.{u}} (q : Y ⟶ S) (a b : Y ⟶ ∐ X)
    (ha : a ≫ Sigma.desc f = q) (hb : b ≫ Sigma.desc f = q) :
    (overPseudofunctor.map a.op.toLoc).toFunctor.obj (assembledObject X f D) ⟶
      (overPseudofunctor.map b.op.toLoc).toFunctor.obj (assembledObject X f D) :=
  Over.homMk (assembledHomLeft X f D q a b ha hb)
    (assembledHomLeft_fac X f D q a b ha hb)

/-- The assembled comparison maps commute with further pullback. -/
theorem assembledHom_pull_source_fac
    {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S)
    (hq : g ≫ q = q') (a : Y ⟶ ∐ X) (ha : a ≫ Sigma.desc f = q)
    (ga : Y' ⟶ ∐ X)
    (hga : g ≫ a = ga) : ga ≫ Sigma.desc f = q' := sorry

/-- The assembled comparison maps commute with further pullback. -/
theorem assembledHom_pull (D : DescentData X f)
    {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S)
    (hq : g ≫ q = q') (a b : Y ⟶ ∐ X) (ha : a ≫ Sigma.desc f = q)
    (hb : b ≫ Sigma.desc f = q) (ga gb : Y' ⟶ ∐ X)
    (hga : g ≫ a = ga) (hgb : g ≫ b = gb) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := overPseudofunctor)
        (assembledHom X f D q a b ha hb) g ga gb =
      assembledHom X f D q' ga gb
        (assembledHom_pull_source_fac X f g q q' hq a ha ga hga)
        (assembledHom_pull_source_fac X f g q q' hq b hb gb hgb) := sorry

/-- The assembled comparison for two equal component maps is the identity. -/
theorem assembledHom_self (D : DescentData X f) {Y : Scheme.{u}}
    (q : Y ⟶ S) (a : Y ⟶ ∐ X) (ha : a ≫ Sigma.desc f = q) :
    assembledHom X f D q a a ha ha = 𝟙 _ := sorry

/-- The assembled comparison maps satisfy the cocycle law. -/
theorem assembledHom_comp (D : DescentData X f) {Y : Scheme.{u}}
    (q : Y ⟶ S) (a b c : Y ⟶ ∐ X) (ha : a ≫ Sigma.desc f = q)
    (hb : b ≫ Sigma.desc f = q) (hc : c ≫ Sigma.desc f = q) :
    assembledHom X f D q a b ha hb ≫ assembledHom X f D q b c hb hc =
      assembledHom X f D q a c ha hc := sorry

/-- Assemble a family-indexed descent datum by taking the coproduct of its component objects and
gluing the pairwise comparison morphisms on coproduct summands. -/
noncomputable def assembleCoproductObj (D : DescentData X f) :
    DescentData (coproductFamily X) (coproductArrow X f) where
  obj _ := assembledObject X f D
  hom _ q _ _ a b ha hb := assembledHom X f D q a b ha hb
  pullHom_hom _ _ g q q' hq _ _ a b ha hb ga gb hga hgb :=
    assembledHom_pull X f D g q q' hq a b ha hb ga gb hga hgb
  hom_self _ q _ a ha := assembledHom_self X f D q a ha
  hom_comp _ q _ _ _ a b c ha hb hc := assembledHom_comp X f D q a b c ha hb hc

/-- Componentwise coproduct maps commute with the assembled descent comparisons. -/
theorem assembledHom_naturality {D E : DescentData X f} (ψ : D ⟶ E)
    {Y : Scheme.{u}} (q : Y ⟶ S) (a b : Y ⟶ ∐ X)
    (ha : a ≫ Sigma.desc f = q) (hb : b ≫ Sigma.desc f = q) :
    (overPseudofunctor.map a.op.toLoc).toFunctor.map (assembledObjectMap X f ψ) ≫
        assembledHom X f E q a b ha hb =
      assembledHom X f D q a b ha hb ≫
        (overPseudofunctor.map b.op.toLoc).toFunctor.map (assembledObjectMap X f ψ) := sorry

/-- Assemble a morphism of family-indexed descent data componentwise on coproducts. -/
noncomputable def assembleCoproductMap {D E : DescentData X f} (ψ : D ⟶ E) :
    assembleCoproductObj X f D ⟶ assembleCoproductObj X f E where
  hom _ := assembledObjectMap X f ψ
  comm _ q _ _ a b ha hb := assembledHom_naturality X f ψ q a b ha hb

/-- Assembly carries an identity morphism to an identity morphism. -/
theorem assembleCoproductMap_id (D : DescentData X f) :
    assembleCoproductMap X f (𝟙 D) = 𝟙 (assembleCoproductObj X f D) := sorry

/-- Assembly carries composition to composition. -/
theorem assembleCoproductMap_comp {D E F : DescentData X f} (ψ : D ⟶ E) (χ : E ⟶ F) :
    assembleCoproductMap X f (ψ ≫ χ) =
      assembleCoproductMap X f ψ ≫ assembleCoproductMap X f χ := sorry

/-- Assemble family-indexed descent data into descent data for the coproduct morphism by taking
coproducts of component objects and morphisms and gluing the overlap comparisons. -/
noncomputable def assembleCoproduct :
    DescentData X f ⥤ DescentData (coproductFamily X) (coproductArrow X f) where
  obj D := assembleCoproductObj X f D
  map ψ := assembleCoproductMap X f ψ
  map_id D := assembleCoproductMap_id X f D
  map_comp ψ χ := assembleCoproductMap_comp X f ψ χ

/-- The sole component of an assembled descent datum is the coproduct of the original component
objects, mapped to `∐ X` by the coproduct of their structure maps. -/
theorem assembleCoproduct_obj (D : DescentData X f) (p : PUnit.{1}) :
    ((assembleCoproduct X f).obj D).obj p = assembledObject X f D := sorry

/-- On underlying schemes, assembly sends a morphism to the coproduct of its component maps. -/
theorem assembleCoproduct_map_left {D E : DescentData X f} (ψ : D ⟶ E) (p : PUnit.{1}) :
    (((assembleCoproduct X f).map ψ).hom p).left = assembledMapLeft X f ψ := sorry

/-- The canonical map from one component to the corresponding pullback of the assembled object. -/
noncomputable def unitComponentLeft (D : DescentData X f) (i : I) :
    (D.obj i).left ⟶ pullback (assembledObject X f D).hom (Sigma.ι X i) :=
  pullback.lift (Sigma.ι (fun j ↦ (D.obj j).left) i) (D.obj i).hom
    (Sigma.ι_desc (fun j ↦ (D.obj j).hom ≫ Sigma.ι X j) i)

/-- The canonical component map to the restriction of the assembled object lies over `X i`. -/
theorem unitComponentLeft_fac (D : DescentData X f) (i : I) :
    unitComponentLeft X f D i ≫ pullback.snd (assembledObject X f D).hom (Sigma.ι X i) =
      (D.obj i).hom := sorry

/-- The canonical component map from a descent datum to the restriction of its assembly. -/
noncomputable def unitComponentMap (D : DescentData X f) (i : I) :
    D.obj i ⟶ ((restrictCoproduct X f).obj ((assembleCoproduct X f).obj D)).obj i :=
  Over.homMk (unitComponentLeft X f D i) (unitComponentLeft_fac X f D i)

/-- The canonical component maps commute with every pairwise descent comparison. -/
theorem unitComponent_comm (D : DescentData X f) {Y : Scheme.{u}} (q : Y ⟶ S)
    {i j : I} (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (overPseudofunctor.map a.op.toLoc).toFunctor.map (unitComponentMap X f D i) ≫
        (((restrictCoproduct X f).obj ((assembleCoproduct X f).obj D)).hom q a b ha hb) =
      D.hom q a b ha hb ≫
        (overPseudofunctor.map b.op.toLoc).toFunctor.map (unitComponentMap X f D j) := sorry

/-- The canonical morphism from a family descent datum to the restriction of its assembled
descent datum. -/
noncomputable def unitComponent (D : DescentData X f) :
    D ⟶ (assembleCoproduct X f ⋙ restrictCoproduct X f).obj D where
  hom i := unitComponentMap X f D i
  comm _ q _ _ a b ha hb := unitComponent_comm X f D q a b ha hb

/-- The cover used to define the inverse of a unit component, obtained by pulling back the
coproduct cover of the assembled object. -/
noncomputable def unitInverseCover (D : DescentData X f) (i : I) :
    Scheme.OpenCover (pullback (assembledObject X f D).hom (Sigma.ι X i)) :=
  (AlgebraicGeometry.sigmaOpenCover (fun j ↦ (D.obj j).left)).pullback₁
    (pullback.fst (assembledObject X f D).hom (Sigma.ι X i))

/-- The map from a member of `unitInverseCover` to its selected component object. -/
noncomputable def unitInverseCoverToSourceComponent (D : DescentData X f) (i j : I) :
    (unitInverseCover X f D i).X j ⟶ (D.obj j).left :=
  (AlgebraicGeometry.sigmaOpenCover (fun k ↦ (D.obj k).left)).pullbackHom
    (pullback.fst (assembledObject X f D).hom (Sigma.ι X i)) j

/-- The map from a member of `unitInverseCover` to the fixed target component. -/
noncomputable def unitInverseCoverToTargetBase (D : DescentData X f) (i j : I) :
    (unitInverseCover X f D i).X j ⟶ X i :=
  (unitInverseCover X f D i).f j ≫
    pullback.snd (assembledObject X f D).hom (Sigma.ι X i)

/-- The map from a member of `unitInverseCover` to the selected source component. -/
noncomputable def unitInverseCoverToSourceBase (D : DescentData X f) (i j : I) :
    (unitInverseCover X f D i).X j ⟶ X j :=
  unitInverseCoverToSourceComponent X f D i j ≫ (D.obj j).hom

/-- The source and target maps on a member of `unitInverseCover` have the same composite to
`S`. -/
theorem unitInverseCover_source_fac (D : DescentData X f) (i j : I) :
    unitInverseCoverToSourceBase X f D i j ≫ f j =
      unitInverseCoverToTargetBase X f D i j ≫ f i := sorry

/-- The canonical lift of a member of `unitInverseCover` to the pullback of its selected source
component. -/
noncomputable def unitInverseLocalSourceLift (D : DescentData X f) (i j : I) :
    (unitInverseCover X f D i).X j ⟶
      pullback (D.obj j).hom (unitInverseCoverToSourceBase X f D i j) :=
  pullback.lift (unitInverseCoverToSourceComponent X f D i j) (𝟙 _)
    (Category.id_comp _).symm

/-- The local inverse to the unit component, obtained from the original descent comparison. -/
noncomputable def unitInverseLocal (D : DescentData X f) (i j : I) :
    (unitInverseCover X f D i).X j ⟶ (D.obj i).left :=
  unitInverseLocalSourceLift X f D i j ≫
    (D.hom (unitInverseCoverToTargetBase X f D i j ≫ f i)
      (unitInverseCoverToSourceBase X f D i j)
      (unitInverseCoverToTargetBase X f D i j)
      (unitInverseCover_source_fac X f D i j) rfl).left ≫
    pullback.fst (D.obj i).hom (unitInverseCoverToTargetBase X f D i j)

/-- The local inverses to a unit component agree on overlaps. -/
theorem unitInverseLocal_compat (D : DescentData X f) (i : I) :
    ∀ j k,
      pullback.fst ((unitInverseCover X f D i).f j)
          ((unitInverseCover X f D i).f k) ≫ unitInverseLocal X f D i j =
      pullback.snd ((unitInverseCover X f D i).f j)
          ((unitInverseCover X f D i).f k) ≫ unitInverseLocal X f D i k := sorry

/-- The explicit underlying inverse to a unit component, obtained by gluing its local descent
maps. -/
noncomputable def unitInverseLeft (D : DescentData X f) (i : I) :
    pullback (assembledObject X f D).hom (Sigma.ι X i) ⟶ (D.obj i).left :=
  (unitInverseCover X f D i).glueMorphisms
    (unitInverseLocal X f D i) (unitInverseLocal_compat X f D i)

/-- The underlying inverse to a unit component lies over `X i`. -/
theorem unitInverseLeft_fac (D : DescentData X f) (i : I) :
    unitInverseLeft X f D i ≫ (D.obj i).hom =
      pullback.snd (assembledObject X f D).hom (Sigma.ι X i) := sorry

/-- The explicit inverse of the unit component over `X i`. -/
noncomputable def unitInverseMap (D : DescentData X f) (i : I) :
    ((restrictCoproduct X f).obj ((assembleCoproduct X f).obj D)).obj i ⟶ D.obj i :=
  Over.homMk (unitInverseLeft X f D i) (unitInverseLeft_fac X f D i)

/-- The inverse unit component maps commute with every pairwise descent comparison. -/
theorem unitInverse_comm (D : DescentData X f) {Y : Scheme.{u}} (q : Y ⟶ S)
    {i j : I} (a : Y ⟶ X i) (b : Y ⟶ X j) (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (overPseudofunctor.map a.op.toLoc).toFunctor.map (unitInverseMap X f D i) ≫
        D.hom q a b ha hb =
      (((restrictCoproduct X f).obj ((assembleCoproduct X f).obj D)).hom q a b ha hb) ≫
        (overPseudofunctor.map b.op.toLoc).toFunctor.map (unitInverseMap X f D j) := sorry

/-- The explicit inverse of the unit component on family descent data. -/
noncomputable def unitComponentInv (D : DescentData X f) :
    (assembleCoproduct X f ⋙ restrictCoproduct X f).obj D ⟶ D where
  hom i := unitInverseMap X f D i
  comm _ q _ _ a b ha hb := unitInverse_comm X f D q a b ha hb

/-- The unit component followed by its explicit inverse is the identity. -/
theorem unitComponent_hom_inv_id (D : DescentData X f) :
    unitComponent X f D ≫ unitComponentInv X f D = 𝟙 D := sorry

/-- The explicit inverse followed by the unit component is the identity. -/
theorem unitComponent_inv_hom_id (D : DescentData X f) :
    unitComponentInv X f D ≫ unitComponent X f D =
      𝟙 ((assembleCoproduct X f ⋙ restrictCoproduct X f).obj D) := sorry

/-- The unit component as an isomorphism with an explicitly constructed inverse. -/
noncomputable def unitComponentIso (D : DescentData X f) :
    D ≅ (assembleCoproduct X f ⋙ restrictCoproduct X f).obj D where
  hom := unitComponent X f D
  inv := unitComponentInv X f D
  hom_inv_id := unitComponent_hom_inv_id X f D
  inv_hom_id := unitComponent_inv_hom_id X f D

/-- The componentwise coproduct-pullback comparison is an isomorphism. -/
instance unitComponent_isIso (D : DescentData X f) : IsIso (unitComponent X f D) :=
  (unitComponentIso X f D).isIso_hom

/-- The unit components are natural in family descent data. -/
theorem unitComponent_naturality {D E : DescentData X f} (ψ : D ⟶ E) :
    ψ ≫ unitComponent X f E = unitComponent X f D ≫
      (assembleCoproduct X f ⋙ restrictCoproduct X f).map ψ := sorry

/-- The canonical unit comparing a family descent datum with the restriction of its assembly. -/
noncomputable def coproductUnitIso :
    𝟭 (DescentData X f) ≅ assembleCoproduct X f ⋙ restrictCoproduct X f :=
  NatIso.ofComponents (unitComponentIso X f)
    (unitComponent_naturality X f)

/-- The coproduct of the pullback projections from all restricted components to the original
object over `∐ X`. -/
noncomputable def counitComponentLeftUnit
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    (assembledObject X f ((restrictCoproduct X f).obj E)).left ⟶
      (E.obj PUnit.unit).left :=
  Sigma.desc fun i ↦ pullback.fst (E.obj PUnit.unit).hom (Sigma.ι X i)

/-- The coproduct of the pullback projections respects the structure map to `∐ X`. -/
theorem counitComponentLeftUnit_fac
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    counitComponentLeftUnit X f E ≫ (E.obj PUnit.unit).hom =
      (assembledObject X f ((restrictCoproduct X f).obj E)).hom := sorry

/-- The component over the sole index of the counit from assembled restrictions to the original
descent datum. -/
noncomputable def counitComponentMapUnit
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    ((assembleCoproduct X f).obj ((restrictCoproduct X f).obj E)).obj PUnit.unit ⟶
      E.obj PUnit.unit :=
  Over.homMk (counitComponentLeftUnit X f E) (counitComponentLeftUnit_fac X f E)

/-- The component of the counit at an arbitrary element of the singleton index type. -/
noncomputable def counitComponentMap
    (E : DescentData (coproductFamily X) (coproductArrow X f)) (p : PUnit.{1}) :
    ((restrictCoproduct X f ⋙ assembleCoproduct X f).obj E).obj p ⟶ E.obj p :=
  match p with
  | .unit => counitComponentMapUnit X f E

/-- The counit component maps commute with the descent comparison for the coproduct morphism. -/
theorem counitComponent_comm
    (E : DescentData (coproductFamily X) (coproductArrow X f)) {Y : Scheme.{u}}
    (q : Y ⟶ S) {p₁ p₂ : PUnit.{1}} (a : Y ⟶ coproductFamily X p₁)
    (b : Y ⟶ coproductFamily X p₂) (ha : a ≫ coproductArrow X f p₁ = q)
    (hb : b ≫ coproductArrow X f p₂ = q) :
    (overPseudofunctor.map a.op.toLoc).toFunctor.map (counitComponentMap X f E p₁) ≫
        E.hom q a b ha hb =
      ((assembleCoproduct X f).obj ((restrictCoproduct X f).obj E)).hom q a b ha hb ≫
        (overPseudofunctor.map b.op.toLoc).toFunctor.map
          (counitComponentMap X f E p₂) := sorry

/-- The canonical counit from the assembly of all restrictions to the original coproduct descent
datum. -/
noncomputable def counitComponent
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    (restrictCoproduct X f ⋙ assembleCoproduct X f).obj E ⟶ E where
  hom p := counitComponentMap X f E p
  comm _ q _ _ a b ha hb := counitComponent_comm X f E q a b ha hb

/-- The pullback of the coproduct cover along the structure map of a coproduct descent datum. -/
noncomputable def counitInverseCover
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    Scheme.OpenCover (E.obj PUnit.unit).left :=
  (AlgebraicGeometry.sigmaOpenCover X).pullback₁ (E.obj PUnit.unit).hom

/-- The map from a member of `counitInverseCover` to the corresponding summand of the assembled
restrictions. -/
noncomputable def counitInverseLocal
    (E : DescentData (coproductFamily X) (coproductArrow X f)) (i : I) :
    (counitInverseCover X f E).X i ⟶
      (assembledObject X f ((restrictCoproduct X f).obj E)).left :=
  Sigma.ι (fun j ↦ (((restrictCoproduct X f).obj E).obj j).left) i

/-- The local maps into the coproduct of restrictions agree on overlaps. -/
theorem counitInverseLocal_compat
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    ∀ i j,
      pullback.fst ((counitInverseCover X f E).f i)
          ((counitInverseCover X f E).f j) ≫ counitInverseLocal X f E i =
      pullback.snd ((counitInverseCover X f E).f i)
          ((counitInverseCover X f E).f j) ≫ counitInverseLocal X f E j := sorry

/-- The explicit underlying inverse to the counit over the singleton index. -/
noncomputable def counitInverseLeftUnit
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    (E.obj PUnit.unit).left ⟶
      (assembledObject X f ((restrictCoproduct X f).obj E)).left :=
  (counitInverseCover X f E).glueMorphisms
    (counitInverseLocal X f E) (counitInverseLocal_compat X f E)

/-- The underlying inverse to the counit lies over `∐ X`. -/
theorem counitInverseLeftUnit_fac
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    counitInverseLeftUnit X f E ≫
        (assembledObject X f ((restrictCoproduct X f).obj E)).hom =
      (E.obj PUnit.unit).hom := sorry

/-- The explicit inverse to the counit over the singleton index. -/
noncomputable def counitInverseMapUnit
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    E.obj PUnit.unit ⟶
      ((assembleCoproduct X f).obj ((restrictCoproduct X f).obj E)).obj PUnit.unit :=
  Over.homMk (counitInverseLeftUnit X f E) (counitInverseLeftUnit_fac X f E)

/-- The explicit inverse to a counit component at an arbitrary singleton index. -/
noncomputable def counitInverseMap
    (E : DescentData (coproductFamily X) (coproductArrow X f)) (p : PUnit.{1}) :
    E.obj p ⟶ ((restrictCoproduct X f ⋙ assembleCoproduct X f).obj E).obj p :=
  match p with
  | .unit => counitInverseMapUnit X f E

/-- The inverse counit component maps commute with the descent comparison for the coproduct
morphism. -/
theorem counitInverse_comm
    (E : DescentData (coproductFamily X) (coproductArrow X f)) {Y : Scheme.{u}}
    (q : Y ⟶ S) {p₁ p₂ : PUnit.{1}} (a : Y ⟶ coproductFamily X p₁)
    (b : Y ⟶ coproductFamily X p₂) (ha : a ≫ coproductArrow X f p₁ = q)
    (hb : b ≫ coproductArrow X f p₂ = q) :
    (overPseudofunctor.map a.op.toLoc).toFunctor.map (counitInverseMap X f E p₁) ≫
        ((assembleCoproduct X f).obj ((restrictCoproduct X f).obj E)).hom q a b ha hb =
      E.hom q a b ha hb ≫
        (overPseudofunctor.map b.op.toLoc).toFunctor.map
          (counitInverseMap X f E p₂) := sorry

/-- The explicit inverse of the counit component on coproduct descent data. -/
noncomputable def counitComponentInv
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    E ⟶ (restrictCoproduct X f ⋙ assembleCoproduct X f).obj E where
  hom p := counitInverseMap X f E p
  comm _ q _ _ a b ha hb := counitInverse_comm X f E q a b ha hb

/-- The counit component followed by its explicit inverse is the identity. -/
theorem counitComponent_hom_inv_id
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    counitComponent X f E ≫ counitComponentInv X f E =
      𝟙 ((restrictCoproduct X f ⋙ assembleCoproduct X f).obj E) := sorry

/-- The explicit inverse followed by the counit component is the identity. -/
theorem counitComponent_inv_hom_id
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    counitComponentInv X f E ≫ counitComponent X f E = 𝟙 E := sorry

/-- The counit component as an isomorphism with an explicitly constructed inverse. -/
noncomputable def counitComponentIso
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    (restrictCoproduct X f ⋙ assembleCoproduct X f).obj E ≅ E where
  hom := counitComponent X f E
  inv := counitComponentInv X f E
  hom_inv_id := counitComponent_hom_inv_id X f E
  inv_hom_id := counitComponent_inv_hom_id X f E

/-- The coproduct of the component pullback projections is an isomorphism of descent data. -/
instance counitComponent_isIso
    (E : DescentData (coproductFamily X) (coproductArrow X f)) :
    IsIso (counitComponent X f E) := (counitComponentIso X f E).isIso_hom

/-- The counit components are natural in descent data for the coproduct morphism. -/
theorem counitComponent_naturality
    {D E : DescentData (coproductFamily X) (coproductArrow X f)} (ψ : D ⟶ E) :
    (restrictCoproduct X f ⋙ assembleCoproduct X f).map ψ ≫ counitComponent X f E =
      counitComponent X f D ≫ ψ := sorry

/-- The canonical counit comparing the assembly of all restrictions with a descent datum for the
coproduct morphism. -/
noncomputable def coproductCounitIso :
    restrictCoproduct X f ⋙ assembleCoproduct X f ≅
      𝟭 (DescentData (coproductFamily X) (coproductArrow X f)) :=
  NatIso.ofComponents (counitComponentIso X f)
    (counitComponent_naturality X f)

/-- The unit and counit satisfy the triangle identity on assembled descent data. -/
theorem coproductTriangle (D : DescentData X f) :
    (assembleCoproduct X f).map ((coproductUnitIso X f).hom.app D) ≫
        (coproductCounitIso X f).hom.app ((assembleCoproduct X f).obj D) =
      𝟙 ((assembleCoproduct X f).obj D) := sorry

/-- The canonical equivalence between descent data for a family of scheme morphisms and descent
data for the induced coproduct morphism. -/
noncomputable def coproductEquivalence :
    DescentData X f ≌ DescentData (coproductFamily X) (coproductArrow X f) where
  functor := assembleCoproduct X f
  inverse := restrictCoproduct X f
  unitIso := coproductUnitIso X f
  counitIso := coproductCounitIso X f
  functor_unitIso_comp D := coproductTriangle X f D

/-- Restriction along the coproduct injections is an equivalence of categories. -/
instance instIsEquivalenceRestrictCoproduct : (restrictCoproduct X f).IsEquivalence :=
  (coproductEquivalence X f).isEquivalence_inverse

/-- Restriction of a coproduct descent datum at `i` is pullback along `Sigma.ι X i`. -/
theorem restrictCoproduct_obj
    (E : DescentData (coproductFamily X) (coproductArrow X f)) (i : I) :
    ((restrictCoproduct X f).obj E).obj i =
      (overPseudofunctor.map (Sigma.ι X i).op.toLoc).toFunctor.obj (E.obj PUnit.unit) := sorry

/-- Under `coproductEquivalence`, the sole component object is the coproduct of the component
schemes, with its induced map to `∐ X`. -/
theorem coproductEquivalence_obj (D : DescentData X f) (p : PUnit.{1}) :
    ((coproductEquivalence X f).functor.obj D).obj p =
      Over.mk (Sigma.desc fun i ↦ (D.obj i).hom ≫ Sigma.ι X i) := sorry

/-- The map assembled by `coproductEquivalence` is characterized on every coproduct injection by
the corresponding component map. -/
theorem coproductEquivalence_map_ι {D E : DescentData X f} (ψ : D ⟶ E) (i : I) :
    Sigma.ι (fun j ↦ (D.obj j).left) i ≫
        ((((coproductEquivalence X f).functor.map ψ).hom PUnit.unit).left) =
      (ψ.hom i).left ≫ Sigma.ι (fun j ↦ (E.obj j).left) i := sorry

/-- Restricting the assembled comparison to the `(i,j)` member of its component cover recovers
the original pairwise descent comparison, transported through the canonical pullbacks. -/
theorem coproductEquivalence_hom_ι (D : DescentData X f) {Y : Scheme.{u}}
    (q : Y ⟶ S) (a b : Y ⟶ ∐ X) (ha : a ≫ Sigma.desc f = q)
    (hb : b ≫ Sigma.desc f = q) (ij : (assembledHomCover X f D a b).I₀) :
    (assembledHomCover X f D a b).f ij ≫ assembledHomLeft X f D q a b ha hb =
      assembledHomLocal X f D q a b ha hb ij := sorry

end DescentData
end Scheme
end AlgebraicGeometry
