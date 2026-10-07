module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.InducedCategory
public import stacks_project.Chap87.Lemma_87_29_3_InverseSystem
public import stacks_project.Chap87.Lemma_87_29_3_Over
public import stacks_project.Chap87.Lemma_87_9_10_Map

/-!
# Colimit of Spec of a finite-type inverse system

An object `(B_I)` of `FiniteTypeInverseSystem A` determines the affine formal
algebraic space `Y = colim Spec(B_I)` over `Spf(A)`, together with the
contravariant comparison functor of Lemma 87.29.3.
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
  sorry

/-- The affine stage `Spec(B_I)` over `S` of an inverse system `B`. -/
def specStage (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) : Over S :=
  Over.mk (specStageHom hA B I)

/-- The underlying scheme of `specStage hA B I` is `Spec(B_I)`. -/
theorem specStage_left (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) :
    (specStage hA B I).left = Spec (B.right.obj (op I)) :=
  sorry

/-- The diagram of affine stages `Spec(B_I)` indexed by weak ideals of
definition. -/
def specStages (B : Under (quotStages A)) : WeakIdealOfDefinition A ⥤ Over S where
  obj I := specStage hA B I
  map {I J} f := Over.homMk (Spec.map (B.right.map f.op)) sorry
  map_id := sorry
  map_comp := sorry

/-- Objects of `specStages hA B` are the stages `specStage hA B I`. -/
theorem specStages_obj (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) :
    (specStages hA B).obj I = specStage hA B I :=
  sorry

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
  sorry

/-- The morphism `Spec(B_I) ⟶ Spec(A ⧸ I)` over `S` induced by the
`A ⧸ I`-algebra structure of a stage. -/
def stageToSpfStage (B : Under (quotStages A)) (I : WeakIdealOfDefinition A) :
    specStage hA B I ⟶ stage A hA I :=
  Over.homMk (Spec.map (B.hom.app (op I))) sorry

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
          naturality := sorry } }

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
        toSpf hA B :=
  sorry

/-- The morphism `Spec(B_I) ⟶ Spec(B'_I)` over `S` induced by an inverse-system
homomorphism. -/
def specStageMap {B B' : Under (quotStages A)} (φ : B' ⟶ B)
    (I : WeakIdealOfDefinition A) :
    specStage hA B I ⟶ specStage hA B' I :=
  Over.homMk (Spec.map (φ.right.app (op I))) sorry

/-- The underlying scheme morphism of `specStageMap` is `Spec` of the stage
homomorphism. -/
theorem specStageMap_left {B B' : Under (quotStages A)} (φ : B' ⟶ B)
    (I : WeakIdealOfDefinition A) :
    (specStageMap hA φ I).left = Spec.map (φ.right.app (op I)) :=
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
          naturality := sorry } }

/-- `colimSpecMap` lies over `Spf(A)`. -/
theorem colimSpecMap_comp {B B' : Under (quotStages A)} (φ : B' ⟶ B) :
    colimSpecMap hA φ ≫ toSpf hA B' = toSpf hA B :=
  sorry

/-- `Spf(A)` is a directed affine thickening colimit. -/
theorem exists_isDirectedAffineThickeningColimit_spf :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D (spf A hA).obj :=
  sorry

/-- `colim Spec(B_I)` is a directed affine thickening colimit. -/
theorem exists_isDirectedAffineThickeningColimit_colimSpec
    (B : FiniteTypeInverseSystem A) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D
        (colimSpec hA B.obj).obj :=
  sorry

/-- The morphism `colim Spec(B_I) ⟶ Spf(A)` is of finite type. -/
instance instFiniteType_toSpf (B : FiniteTypeInverseSystem A) :
    FormalAlgebraicSpace.FiniteType (toSpf hA B.obj).hom :=
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
      (MorphismProperty.Over.homMk (colimSpecMap hA f.unop.hom).hom sorry)
  map_id := sorry
  map_comp := sorry

/-- The object map of `spfFiniteTypeSystem` sends `(B_I)` to
`colim Spec(B_I)` over `Spf(A)`. -/
theorem spfFiniteTypeSystem_obj (B : FiniteTypeInverseSystem A) :
    ((spfFiniteTypeSystem hA).obj (op B)).obj.hom = (toSpf hA B.obj).hom :=
  sorry

/-- The morphism map of `spfFiniteTypeSystem` is `colim Spec` of the inverse
system homomorphism. -/
theorem spfFiniteTypeSystem_map {B B' : FiniteTypeInverseSystem A}
    (f : B ⟶ B') :
    ((spfFiniteTypeSystem hA).map f.op).hom.left = (colimSpecMap hA f.hom).hom :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
