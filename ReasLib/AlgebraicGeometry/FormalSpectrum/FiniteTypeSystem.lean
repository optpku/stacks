/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.InducedCategory
public import ReasLib.AlgebraicGeometry.FormalSpectrum.FiniteTypeInverseSystem
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.FiniteTypeOver
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Colimit

/-!
# Colimit of Spec of a finite-type inverse system

An object `(B_I)` of `FiniteTypeInverseSystem A` determines the affine formal
algebraic space `Y = colim Spec(B_I)` over `Spf(A)`, together with the
contravariant comparison functor to the finite-type slice.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- The structure morphism `Spec(B_I) ⟶ S` of a stage of an inverse system. -/
def specStageHom (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) :
    Spec (B.right.obj (op I)) ⟶ S :=
  Spec.map (B.hom.app (op I)) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.ideal)) ≫ hA

/-- The structure morphism of `specStageHom` factors through `Spec(A ⧸ I)`. -/
theorem specStageHom_comp (B : Under (quotStages A))
    (I : WeakIdealOfDefinition A) :
    specStageHom hA B I =
      Spec.map (B.hom.app (op I)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.ideal)) ≫ hA :=
  rfl

/-- The affine stage `Spec(B_I)` over `S` of an inverse system `B`. -/
def specStage (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) : Over S :=
  Over.mk (specStageHom hA B I)

/-- The underlying scheme of `specStage hA B I` is `Spec(B_I)`. -/
theorem specStage_left (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) :
    (specStage hA B I).left = Spec (B.right.obj (op I)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A spectrum transition commutes with the structure morphisms to the base. -/
theorem specStages_map_comm (B : Under (quotStages A))
    {I J : WeakIdealOfDefinition A} (f : I ⟶ J) :
    Spec.map (B.right.map f.op) ≫ (specStage hA B J).hom =
      (specStage hA B I).hom := by
  have hquot : CommRingCat.ofHom (Ideal.Quotient.mk J.ideal) ≫
      (quotStages A).map f.op = CommRingCat.ofHom (Ideal.Quotient.mk I.ideal) := by
    apply CommRingCat.hom_ext
    exact Ideal.Quotient.factor_comp_mk (leOfHom f)
  have hbase : CommRingCat.ofHom (Ideal.Quotient.mk J.ideal) ≫
      B.hom.app (op J) ≫ B.right.map f.op =
      CommRingCat.ofHom (Ideal.Quotient.mk I.ideal) ≫ B.hom.app (op I) := by
    erw [← B.hom.naturality f.op, ← Category.assoc, hquot]
  change Spec.map (B.right.map f.op) ≫
      (Spec.map (B.hom.app (op J)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.ideal)) ≫ hA) =
    Spec.map (B.hom.app (op I)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.ideal)) ≫ hA
  simpa! only [Spec.map_comp, Category.assoc]
    using congrArg (fun k ↦ Spec.map k ≫ hA) hbase

/-- The spectrum transition associated to an identity is the identity over the base. -/
theorem specStages_map_id (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) :
    Over.homMk (Spec.map (B.right.map (𝟙 I).op))
        (specStages_map_comm hA B (𝟙 I)) = 𝟙 (specStage hA B I) := by
  apply Over.OverMorphism.ext
  change Spec.map (B.right.map (𝟙 I).op) = 𝟙 _
  simp

/-- Spectrum transitions preserve composition in the weak-ideal index. -/
theorem specStages_map_comp (B : Under (quotStages A))
    {I J K : WeakIdealOfDefinition A} (f : I ⟶ J) (g : J ⟶ K) :
    Over.homMk (U := specStage hA B I) (V := specStage hA B K)
        (Spec.map (B.right.map (f ≫ g).op))
        (specStages_map_comm hA B (f ≫ g)) =
      Over.homMk (U := specStage hA B I) (V := specStage hA B J)
          (Spec.map (B.right.map f.op)) (specStages_map_comm hA B f) ≫
        Over.homMk (U := specStage hA B J) (V := specStage hA B K)
          (Spec.map (B.right.map g.op)) (specStages_map_comm hA B g) := by
  apply Over.OverMorphism.ext
  change Spec.map (B.right.map (f ≫ g).op) =
    Spec.map (B.right.map f.op) ≫ Spec.map (B.right.map g.op)
  simp

/-- The diagram of affine stages `Spec(B_I)` indexed by weak ideals of
definition. -/
def specStages (B : Under (quotStages A)) : WeakIdealOfDefinition A ⥤ Over S where
  obj I := specStage hA B I
  map {I J} f :=
    Over.homMk (Spec.map (B.right.map f.op)) (specStages_map_comm hA B f)
  map_id := specStages_map_id hA B
  map_comp := specStages_map_comp hA B

/-- Objects of `specStages hA B` are the stages `specStage hA B I`. -/
theorem specStages_obj (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) :
    (specStages hA B).obj I = specStage hA B I :=
  rfl

/-- The sheaf colimit `colim Spec(B_I)` of the affine stages of `B`. -/
def colimSpec (B : Under (quotStages A)) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  colimit
    (specStages hA B ⋙ yoneda ⋙
      presheafToSheaf (Scheme.fppfTopology.over S) (Type u))

/-- `colimSpec hA B` is the sheaf colimit of sheafified Yoneda of
`specStages hA B`. -/
theorem colimSpec_eq (B : Under (quotStages A)) :
    colimSpec hA B =
      colimit
        (specStages hA B ⋙ yoneda ⋙
          presheafToSheaf (Scheme.fppfTopology.over S) (Type u)) :=
  rfl

/-- The stage algebra map induces a spectrum map over the base scheme. -/
theorem stageToSpfStage_comm (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) :
    Spec.map (B.hom.app (op I)) ≫ (stage A hA I).hom =
      (specStage hA B I).hom := by
  rfl

/-- The morphism `Spec(B_I) ⟶ Spec(A ⧸ I)` over `S` induced by the
`A ⧸ I`-algebra structure of a stage. -/
def stageToSpfStage (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) :
    specStage hA B I ⟶ stage A hA I :=
  Over.homMk (Spec.map (B.hom.app (op I))) (stageToSpfStage_comm hA B I)

/-- The stage algebra maps followed by the formal-spectrum legs form a cocone. -/
theorem toSpf_naturality (B : Under (quotStages A))
    {I J : WeakIdealOfDefinition A} (f : I ⟶ J) :
    (specStages hA B ⋙ yoneda ⋙
        presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map f ≫
      ((presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (stageToSpfStage hA B J)) ≫ spfι A hA J) =
      ((presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (stageToSpfStage hA B I)) ≫ spfι A hA I) ≫
        𝟙 (spf A hA) := by
  have hw : (specStages hA B).map f ≫ stageToSpfStage hA B J =
      stageToSpfStage hA B I ≫ (thickenings A hA).map f := by
    apply Over.OverMorphism.ext
    change Spec.map (B.right.map f.op) ≫ Spec.map (B.hom.app (op J)) =
      Spec.map (B.hom.app (op I)) ≫ Spec.map ((quotStages A).map f.op)
    rw [← Spec.map_comp, ← Spec.map_comp, B.hom.naturality f.op]
  change (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
      (yoneda.map ((specStages hA B).map f)) ≫ _ = _
  erw [Category.comp_id, ← Category.assoc, ← Functor.map_comp, ← yoneda.map_comp, hw,
    yoneda.map_comp, Functor.map_comp, Category.assoc]
  congr 1
  exact colimit.w
    (thickenings A hA ⋙ yoneda ⋙
      presheafToSheaf (Scheme.fppfTopology.over S) (Type u)) f

/-- The morphism `colim Spec(B_I) ⟶ Spf(A)` induced by the stage maps
`Spec(B_I) ⟶ Spec(A ⧸ I)`. -/
def toSpf (B : Under (quotStages A)) : colimSpec hA B ⟶ spf A hA :=
  colimit.desc
    (specStages hA B ⋙ yoneda ⋙
      presheafToSheaf (Scheme.fppfTopology.over S) (Type u))
    { pt := spf A hA
      ι :=
        { app I :=
            (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
                (yoneda.map (stageToSpfStage hA B I)) ≫
              spfι A hA I
          naturality := fun _ _ f ↦ toSpf_naturality hA B f } }

/-- Stage maps `Spec(B_I) ⟶ Spec(A ⧸ I)` compose with the cocone of `Spf(A)` to
the cocone of `toSpf hA B`. -/
theorem toSpf_w (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) :
    (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (stageToSpfStage hA B I)) ≫
        spfι A hA I =
      colimit.ι
          (specStages hA B ⋙ yoneda ⋙
            presheafToSheaf (Scheme.fppfTopology.over S) (Type u))
          I ≫
        toSpf hA B := by
  unfold toSpf
  symm
  apply colimit.ι_desc

/-- A component of an inverse-system morphism induces a spectrum map over the base. -/
theorem specStageMap_comm {B B' : Under (quotStages A)} (φ : B' ⟶ B)
    (I : WeakIdealOfDefinition A) :
    Spec.map (φ.right.app (op I)) ≫ (specStage hA B' I).hom =
      (specStage hA B I).hom := by
  have hw : B'.hom.app (op I) ≫ φ.right.app (op I) = B.hom.app (op I) :=
    congrArg (fun α ↦ α.app (op I)) (Under.w φ)
  change Spec.map (φ.right.app (op I)) ≫
      (Spec.map (B'.hom.app (op I)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.ideal)) ≫ hA) = _
  erw [← Spec.map_comp_assoc, hw]
  rfl

/-- The morphism `Spec(B_I) ⟶ Spec(B'_I)` over `S` induced by an inverse-system
homomorphism. -/
def specStageMap {B B' : Under (quotStages A)} (φ : B' ⟶ B)
    (I : WeakIdealOfDefinition A) :
    specStage hA B I ⟶ specStage hA B' I :=
  Over.homMk (Spec.map (φ.right.app (op I))) (specStageMap_comm hA φ I)

/-- The underlying scheme morphism of `specStageMap` is `Spec` of the stage
homomorphism. -/
theorem specStageMap_left {B B' : Under (quotStages A)} (φ : B' ⟶ B)
    (I : WeakIdealOfDefinition A) :
    (specStageMap hA φ I).left = Spec.map (φ.right.app (op I)) :=
  rfl

/-- Stagewise spectrum maps followed by colimit legs form a cocone. -/
theorem colimSpecMap_naturality {B B' : Under (quotStages A)} (φ : B' ⟶ B)
    {I J : WeakIdealOfDefinition A} (f : I ⟶ J) :
    (specStages hA B ⋙ yoneda ⋙
        presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map f ≫
      ((presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (specStageMap hA φ J)) ≫
        colimit.ι (specStages hA B' ⋙ yoneda ⋙
          presheafToSheaf (Scheme.fppfTopology.over S) (Type u)) J) =
      ((presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
          (yoneda.map (specStageMap hA φ I)) ≫
        colimit.ι (specStages hA B' ⋙ yoneda ⋙
          presheafToSheaf (Scheme.fppfTopology.over S) (Type u)) I) ≫
        𝟙 (colimSpec hA B') := by
  have hw : (specStages hA B).map f ≫ specStageMap hA φ J =
      specStageMap hA φ I ≫ (specStages hA B').map f := by
    apply Over.OverMorphism.ext
    change Spec.map (B.right.map f.op) ≫ Spec.map (φ.right.app (op J)) =
      Spec.map (φ.right.app (op I)) ≫ Spec.map (B'.right.map f.op)
    rw [← Spec.map_comp, ← Spec.map_comp, φ.right.naturality f.op]
  change (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
      (yoneda.map ((specStages hA B).map f)) ≫ _ = _
  erw [Category.comp_id, ← Category.assoc, ← Functor.map_comp, ← yoneda.map_comp, hw,
    yoneda.map_comp, Functor.map_comp, Category.assoc]
  congr 1
  exact colimit.w
    (specStages hA B' ⋙ yoneda ⋙
      presheafToSheaf (Scheme.fppfTopology.over S) (Type u)) f

/-- A morphism of inverse systems induces `colim Spec(B_I) ⟶ colim Spec(B'_I)`
by applying `Spec` stagewise. -/
def colimSpecMap {B B' : Under (quotStages A)} (φ : B' ⟶ B) :
    colimSpec hA B ⟶ colimSpec hA B' :=
  colimit.desc
    (specStages hA B ⋙ yoneda ⋙
      presheafToSheaf (Scheme.fppfTopology.over S) (Type u))
    { pt := colimSpec hA B'
      ι :=
        { app I :=
            (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
                (yoneda.map (specStageMap hA φ I)) ≫
              colimit.ι
                (specStages hA B' ⋙ yoneda ⋙
                  presheafToSheaf (Scheme.fppfTopology.over S) (Type u))
                I
          naturality := fun _ _ f ↦ colimSpecMap_naturality hA φ f } }

set_option backward.isDefEq.respectTransparency false in
/-- A colimit leg followed by `colimSpecMap` is the induced map at that stage. -/
@[reassoc]
theorem colimSpecMap_ι {B B' : Under (quotStages A)} (φ : B' ⟶ B)
    (I : WeakIdealOfDefinition A) :
    colimit.ι (specStages hA B ⋙ yoneda ⋙
        presheafToSheaf (Scheme.fppfTopology.over S) (Type u)) I ≫
      colimSpecMap hA φ =
    (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
        (yoneda.map (specStageMap hA φ I)) ≫
      colimit.ι (specStages hA B' ⋙ yoneda ⋙
        presheafToSheaf (Scheme.fppfTopology.over S) (Type u)) I := by
  unfold colimSpecMap
  apply colimit.ι_desc

set_option backward.isDefEq.respectTransparency false in
/-- `colimSpecMap` lies over `Spf(A)`. -/
theorem colimSpecMap_comp {B B' : Under (quotStages A)} (φ : B' ⟶ B) :
    colimSpecMap hA φ ≫ toSpf hA B' = toSpf hA B := by
  have hw (I : WeakIdealOfDefinition A) :
      specStageMap hA φ I ≫ stageToSpfStage hA B' I = stageToSpfStage hA B I := by
    apply Over.OverMorphism.ext
    change Spec.map (φ.right.app (op I)) ≫ Spec.map (B'.hom.app (op I)) =
      Spec.map (B.hom.app (op I))
    rw [← Spec.map_comp]
    exact congrArg Spec.map (congrArg (fun α ↦ α.app (op I)) (Under.w φ))
  apply colimit.hom_ext
  intro I
  rw [colimSpecMap_ι_assoc, ← toSpf_w hA B' I, ← toSpf_w hA B I,
    ← Category.assoc, ← Functor.map_comp, ← yoneda.map_comp, hw I]

/-- `colim Spec(B_I)` is a directed affine thickening colimit. -/
theorem exists_isDirectedAffineThickeningColimit_colimSpec
    (B : FiniteTypeInverseSystem A) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D
        (colimSpec hA B.obj).obj :=
  sorry

/-- The sheaf colimit of a finite-type inverse system is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_colimSpec (B : FiniteTypeInverseSystem A) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (colimSpec hA B.obj).obj :=
  sorry

/-- The morphism `colim Spec(B_I) ⟶ Spf(A)` is of finite type. -/
instance instFiniteType_toSpf (B : FiniteTypeInverseSystem A) :
    FormalAlgebraicSpace.FiniteType (toSpf hA B.obj).hom :=
  sorry

/-- The induced colimit map commutes with the structural arrows to the formal spectrum. -/
theorem spfFiniteTypeSystem_map_comm {B B' : FiniteTypeInverseSystem A} (f : B ⟶ B') :
    (colimSpecMap hA f.hom).hom ≫ (toSpf hA B.obj).hom = (toSpf hA B'.obj).hom := by
  exact congrArg (fun k ↦ k.hom) (colimSpecMap_comp hA f.hom)

set_option backward.isDefEq.respectTransparency false in
/-- The colimit map induced by an identity inverse-system morphism is the identity. -/
theorem spfFiniteTypeSystem_map_id (B : FiniteTypeInverseSystem A) :
    (colimSpecMap hA (𝟙 B.obj)).hom = 𝟙 (colimSpec hA B.obj).obj := by
  have hw (I : WeakIdealOfDefinition A) :
      specStageMap hA (𝟙 B.obj) I = 𝟙 (specStage hA B.obj I) := by
    apply Over.OverMorphism.ext
    change Spec.map (𝟙 _) = 𝟙 _
    exact Spec.map_id _
  have hmap : colimSpecMap hA (𝟙 B.obj) = 𝟙 (colimSpec hA B.obj) := by
    apply colimit.hom_ext
    intro I
    erw [colimSpecMap_ι, hw I, yoneda.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  exact congrArg (fun k ↦ k.hom) hmap

set_option backward.isDefEq.respectTransparency false in
/-- Colimit maps reverse composition of inverse-system morphisms. -/
theorem spfFiniteTypeSystem_map_comp {B B' B'' : FiniteTypeInverseSystem A}
    (f : B ⟶ B') (g : B' ⟶ B'') :
    (colimSpecMap hA (f ≫ g).hom).hom =
      (colimSpecMap hA g.hom).hom ≫ (colimSpecMap hA f.hom).hom := by
  have hw (I : WeakIdealOfDefinition A) :
      specStageMap hA (f ≫ g).hom I =
        specStageMap hA g.hom I ≫ specStageMap hA f.hom I := by
    apply Over.OverMorphism.ext
    change Spec.map (f.hom.right.app (op I) ≫ g.hom.right.app (op I)) =
      Spec.map (g.hom.right.app (op I)) ≫ Spec.map (f.hom.right.app (op I))
    exact Spec.map_comp _ _
  have hmap : colimSpecMap hA (f ≫ g).hom =
      colimSpecMap hA g.hom ≫ colimSpecMap hA f.hom := by
    apply colimit.hom_ext
    intro I
    rw [colimSpecMap_ι, colimSpecMap_ι_assoc, colimSpecMap_ι,
      hw I, yoneda.map_comp, Functor.map_comp, Category.assoc]
  exact congrArg (fun k ↦ k.hom) hmap

/-- The functor sending a finite-type inverse system `(B_I)` to
`colim Spec(B_I)` over `Spf(A)`. It is contravariant on inverse-system
homomorphisms, matching the variance of `Spec`. -/
def spfFiniteTypeSystem :
    (FiniteTypeInverseSystem A)ᵒᵖ ⥤ AffineFiniteTypeOver (spf A hA).obj where
  obj B :=
    AffineFiniteTypeOver.mk (toSpf hA B.unop.obj).hom
      (exists_isDirectedAffineThickeningColimit_colimSpec hA B.unop)
  map {B B'} f :=
    InducedCategory.homMk
      (MorphismProperty.Over.homMk (colimSpecMap hA f.unop.hom).hom
        (spfFiniteTypeSystem_map_comm hA f.unop))
  map_id B := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact spfFiniteTypeSystem_map_id hA B.unop
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact spfFiniteTypeSystem_map_comp hA g.unop f.unop

/-- The object map of `spfFiniteTypeSystem` sends `(B_I)` to
`colim Spec(B_I)` over `Spf(A)`. -/
theorem spfFiniteTypeSystem_obj (B : FiniteTypeInverseSystem A) :
    ((spfFiniteTypeSystem hA).obj (op B)).obj.hom = (toSpf hA B.obj).hom :=
  rfl

/-- The morphism map of `spfFiniteTypeSystem` is `colim Spec` of the inverse
system homomorphism. -/
theorem spfFiniteTypeSystem_map {B B' : FiniteTypeInverseSystem A}
    (f : B ⟶ B') :
    ((spfFiniteTypeSystem hA).map f.op).hom.left = (colimSpecMap hA f.hom).hom :=
  rfl

/-- The spectrum-colimit comparison is an anti-equivalence over the formal spectrum. -/
instance instIsEquivalence_spfFiniteTypeSystem :
    (spfFiniteTypeSystem hA).IsEquivalence :=
  sorry

set_option backward.isDefEq.respectTransparency false in
/-- Composing a finite-type map with an isomorphism of its target preserves finite type. -/
private theorem finiteType_comp_iso {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) [FormalAlgebraicSpace.FiniteType f] (e : Y ≅ Z) :
    FormalAlgebraicSpace.FiniteType (f ≫ e.hom) := by
  have hrep : AlgebraicSpace.representableByAlgebraicSpaces e.hom := by
    intro U ξ
    exact AlgebraicSpace.IsAlgebraicSpace.of_iso (asIso (pullback.fst ξ e.hom))
  have hiso : FormalAlgebraicSpace.FiniteType e.hom := by
    refine ⟨hrep, ?_⟩
    intro U ξ
    let ePullback : pullback ξ e.hom ≅ yoneda.obj U :=
      asIso (pullback.fst ξ e.hom)
    letI : IsIso (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom hrep ξ) :=
      ⟨⟨ePullback.inv, ePullback.hom_inv_id, ePullback.inv_hom_id⟩⟩
    exact AlgebraicSpace.FiniteType.of_isIso _
  letI := hiso
  exact FormalAlgebraicSpace.finiteType_comp f e.hom

/-- The structural map of a finite-type system remains of finite type after
identifying the formal spectrum with the base. -/
instance instFiniteType_toBase {X : (Over S)ᵒᵖ ⥤ Type u}
    (eX : (spf A hA).obj ≅ X) (B : FiniteTypeInverseSystem A) :
    FormalAlgebraicSpace.FiniteType ((toSpf hA B.obj).hom ≫ eX.hom) := by
  exact finiteType_comp_iso (toSpf hA B.obj).hom eX

/-- The spectrum-colimit comparison over a base identified with the formal spectrum. -/
def spfFiniteTypeSystemOver {X : (Over S)ᵒᵖ ⥤ Type u} (eX : (spf A hA).obj ≅ X) :
    (FiniteTypeInverseSystem A)ᵒᵖ ⥤ AffineFiniteTypeOver X where
  obj B :=
    AffineFiniteTypeOver.mk ((toSpf hA B.unop.obj).hom ≫ eX.hom)
      (exists_isDirectedAffineThickeningColimit_colimSpec hA B.unop)
  map {B B'} f :=
    InducedCategory.homMk
      (MorphismProperty.Over.homMk (colimSpecMap hA f.unop.hom).hom (by
        change (colimSpecMap hA f.unop.hom).hom ≫
            ((toSpf hA B'.unop.obj).hom ≫ eX.hom) =
          (toSpf hA B.unop.obj).hom ≫ eX.hom
        rw [← Category.assoc, spfFiniteTypeSystem_map_comm hA f.unop]))
  map_id B := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact spfFiniteTypeSystem_map_id hA B.unop
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact spfFiniteTypeSystem_map_comp hA g.unop f.unop

set_option backward.isDefEq.respectTransparency false in
/-- The spectrum-colimit comparison is an anti-equivalence over any base
identified with the associated formal spectrum. -/
instance instIsEquivalence_spfFiniteTypeSystemOver {X : (Over S)ᵒᵖ ⥤ Type u}
    (eX : (spf A hA).obj ≅ X) :
    (spfFiniteTypeSystemOver hA eX).IsEquivalence := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    intro B B' f g h
    apply (spfFiniteTypeSystem hA).map_injective
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun k ↦ k.hom.left) h
  · constructor
    intro B B' f
    let f₀ : (spfFiniteTypeSystem hA).obj B ⟶ (spfFiniteTypeSystem hA).obj B' :=
      InducedCategory.homMk (MorphismProperty.Over.homMk f.hom.left (by
        apply (cancel_mono eX.hom).mp
        have hw : f.hom.left ≫ ((toSpf hA B'.unop.obj).hom ≫ eX.hom) =
            (toSpf hA B.unop.obj).hom ≫ eX.hom := MorphismProperty.Over.w f.hom
        exact (Category.assoc _ _ _).trans hw))
    obtain ⟨g, hg⟩ := (spfFiniteTypeSystem hA).map_surjective f₀
    refine ⟨g, ?_⟩
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun k ↦ k.hom.left) hg
  · constructor
    intro U
    letI : FormalAlgebraicSpace.FiniteType (U.obj.hom ≫ eX.inv) :=
      finiteType_comp_iso U.obj.hom eX.symm
    let U₀ : AffineFiniteTypeOver (spf A hA).obj :=
      ⟨MorphismProperty.Over.mk ⊤ (U.obj.hom ≫ eX.inv) inferInstance, U.property⟩
    obtain ⟨B, ⟨eB⟩⟩ :=
      CategoryTheory.Functor.EssSurj.mem_essImage (spfFiniteTypeSystem hA) U₀
    let eLeft : (colimSpec hA B.unop.obj).obj ≅ U.obj.left :=
      { hom := eB.hom.hom.left
        inv := eB.inv.hom.left
        hom_inv_id := congrArg (fun k ↦ k.hom.left) eB.hom_inv_id
        inv_hom_id := congrArg (fun k ↦ k.hom.left) eB.inv_hom_id }
    refine ⟨B, ⟨ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk eLeft ?_)⟩⟩
    have hw := congrArg (fun k ↦ k ≫ eX.hom) (MorphismProperty.Over.w eB.hom.hom)
    change (eLeft.hom ≫ (U.obj.hom ≫ eX.inv)) ≫ eX.hom =
      (toSpf hA B.unop.obj).hom ≫ eX.hom at hw
    change eLeft.hom ≫ U.obj.hom = (toSpf hA B.unop.obj).hom ≫ eX.hom
    erw [Category.assoc, Category.assoc, eX.inv_hom_id, Category.comp_id] at hw
    exact hw

end AlgebraicGeometry.AffineFormalAlgebraicSpace
