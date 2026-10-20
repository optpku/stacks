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

/-- A spectrum transition commutes with the structure morphisms to the base. -/
theorem specStages_map_comm (B : Under (quotStages A))
    {I J : WeakIdealOfDefinition A} (f : I ⟶ J) :
    Spec.map (B.right.map f.op) ≫ (specStage hA B J).hom =
      (specStage hA B I).hom :=
  sorry

/-- The spectrum transition associated to an identity is the identity over the base. -/
theorem specStages_map_id (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) :
    Over.homMk (Spec.map (B.right.map (𝟙 I).op))
        (specStages_map_comm hA B (𝟙 I)) = 𝟙 (specStage hA B I) :=
  sorry

/-- Spectrum transitions preserve composition in the weak-ideal index. -/
theorem specStages_map_comp (B : Under (quotStages A))
    {I J K : WeakIdealOfDefinition A} (f : I ⟶ J) (g : J ⟶ K) :
    Over.homMk (U := specStage hA B I) (V := specStage hA B K)
        (Spec.map (B.right.map (f ≫ g).op))
        (specStages_map_comm hA B (f ≫ g)) =
      Over.homMk (U := specStage hA B I) (V := specStage hA B J)
          (Spec.map (B.right.map f.op)) (specStages_map_comm hA B f) ≫
        Over.homMk (U := specStage hA B J) (V := specStage hA B K)
          (Spec.map (B.right.map g.op)) (specStages_map_comm hA B g) :=
  sorry

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
      (specStage hA B I).hom :=
  sorry

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
        𝟙 (spf A hA) :=
  sorry

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
      (specStage hA B I).hom :=
  sorry

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
        𝟙 (colimSpec hA B') :=
  sorry

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

/-- `colimSpecMap` lies over `Spf(A)`. -/
theorem colimSpecMap_comp {B B' : Under (quotStages A)} (φ : B' ⟶ B) :
    colimSpecMap hA φ ≫ toSpf hA B' = toSpf hA B :=
  sorry

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
    (colimSpecMap hA f.hom).hom ≫ (toSpf hA B.obj).hom = (toSpf hA B'.obj).hom :=
  sorry

/-- The colimit map induced by an identity inverse-system morphism is the identity. -/
theorem spfFiniteTypeSystem_map_id (B : FiniteTypeInverseSystem A) :
    (colimSpecMap hA (𝟙 B.obj)).hom = 𝟙 (colimSpec hA B.obj).obj :=
  sorry

/-- Colimit maps reverse composition of inverse-system morphisms. -/
theorem spfFiniteTypeSystem_map_comp {B B' B'' : FiniteTypeInverseSystem A}
    (f : B ⟶ B') (g : B' ⟶ B'') :
    (colimSpecMap hA (f ≫ g).hom).hom =
      (colimSpecMap hA g.hom).hom ≫ (colimSpecMap hA f.hom).hom :=
  sorry

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

/-- The structural map of a finite-type system remains of finite type after
identifying the formal spectrum with the base. -/
instance instFiniteType_toBase {X : (Over S)ᵒᵖ ⥤ Type u}
    (eX : (spf A hA).obj ≅ X) (B : FiniteTypeInverseSystem A) :
    FormalAlgebraicSpace.FiniteType ((toSpf hA B.obj).hom ≫ eX.hom) :=
  sorry

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

/-- The spectrum-colimit comparison is an anti-equivalence over any base
identified with the associated formal spectrum. -/
instance instIsEquivalence_spfFiniteTypeSystemOver {X : (Over S)ᵒᵖ ⥤ Type u}
    (eX : (spf A hA).obj ≅ X) :
    (spfFiniteTypeSystemOver hA eX).IsEquivalence :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
