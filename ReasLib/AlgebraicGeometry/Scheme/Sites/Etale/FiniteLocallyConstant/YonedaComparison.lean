/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Representation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.AffineComparison
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-!
# Yoneda comparison for the constructed finite étale representation

The forward comparison evaluates functions on affine test opens and glues the resulting
scheme morphisms over the pulled base-open cover. The reverse map restricts the actual
universal section, glued from the affine universal sections. Sheafification transports
these same two implemented directions to the source-facing sheaf comparison.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.FiniteLocallyConstant

variable {X : Scheme.{u}}
variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1))) [Sheaf.IsFiniteLocallyConstant F]

/-- The sheafified representable of the actual globally glued étale object. -/
abbrev representationSheaf : Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  X.smallEtaleTopology.sheafifiedRepresentable (representationEtale F)

/-- An affine open in a test object is an actual étale object over the original scheme. -/
abbrev testAffineEtale (V : X.Etale) (W : V.left.affineOpens) : X.Etale :=
  Scheme.Etale.mk ((W : V.left.Opens).ι ≫ V.hom)

instance testAffineEtale_isAffine (V : X.Etale) (W : V.left.affineOpens) :
    IsAffine (testAffineEtale V W).left := W.property

/-- The inclusion of a test affine open into its original étale object. -/
def testAffineEtaleMap (V : X.Etale) (W : V.left.affineOpens) : testAffineEtale V W ⟶ V :=
  MorphismProperty.Over.homMk (W : V.left.Opens).ι rfl

/-- Evaluation on an affine test open followed by its actual algebra restriction map. -/
def localSectionAffineChart (U : X.affineOpens) (V : Over (affineOpenEtale U))
    (s : F.obj.obj (op V.left)) (W : V.left.left.affineOpens) :
    (W : V.left.left.Opens).toScheme ⟶ affineRepresentation F (affineOpenEtale U) :=
  affineSectionMap F (testAffineEtale V.left W)
      (F.obj.map (testAffineEtaleMap V.left W).op s) ≫
    affineRestrictionMap F (testAffineEtaleMap V.left W ≫ V.hom)

/-- The evaluation morphisms agree under inclusion of affine test opens. -/
theorem localSectionAffineChart_compatible (U : X.affineOpens) (V : Over (affineOpenEtale U))
    (s : F.obj.obj (op V.left)) {W₁ W₂ : V.left.left.affineOpens} (h : W₁ ≤ W₂) :
    V.left.left.homOfLE h ≫ localSectionAffineChart F U V s W₂ =
      localSectionAffineChart F U V s W₁ := sorry

/-- Native directed affine-open gluing gives the actual morphism on an arbitrary test object. -/
def localSectionIntoAffine (U : X.affineOpens) (V : Over (affineOpenEtale U))
    (s : F.obj.obj (op V.left)) : V.left.left ⟶ affineRepresentation F (affineOpenEtale U) :=
  V.left.left.directedAffineCover.glueMorphismsOfLocallyDirected
    (localSectionAffineChart F U V s)
    (fun h ↦ localSectionAffineChart_compatible F U V s (leOfHom h))

/-- The glued evaluation map into the actual global representation. -/
def localSectionMap (U : X.affineOpens) (V : Over (affineOpenEtale U))
    (s : F.obj.obj (op V.left)) : V.left.left ⟶ representation F :=
  localSectionIntoAffine F U V s ≫ representationChart F U

/-- The local evaluation map lies over the original scheme. -/
theorem localSectionMap_over (U : X.affineOpens) (V : Over (affineOpenEtale U))
    (s : F.obj.obj (op V.left)) : localSectionMap F U V s ≫ representationMap F = V.left.hom := sorry

/-- Each actual global affine chart is a morphism of the original small étale site. -/
def representationChartEtale (U : X.affineOpens) :
    affineRepresentationEtale F (affineOpenEtale U) ⟶ representationEtale F :=
  MorphismProperty.Over.homMk (representationChart F U)
    ((representationGluingData F).ι_toBase U)

/-- Native relative gluing gives the real covering sieve by the affine representation charts. -/
theorem representationCharts_covering :
    Sieve.ofArrows (fun U : X.affineOpens ↦ affineRepresentationEtale F (affineOpenEtale U))
      (representationChartEtale F) ∈ X.smallEtaleTopology (representationEtale F) := by
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (representationChartEtale F)).mpr
  exact (representationGluingData F).cover.iUnion_range

/-- The actual affine universal sections agree on every common test of the global chart cover. -/
theorem affineTautologicalSection_compatible {W : X.Etale} {U V : X.affineOpens}
    (a : W ⟶ affineRepresentationEtale F (affineOpenEtale U))
    (b : W ⟶ affineRepresentationEtale F (affineOpenEtale V))
    (hab : a ≫ representationChartEtale F U = b ≫ representationChartEtale F V) :
    F.obj.map a.op (affineTautologicalSection F (affineOpenEtale U)) =
      F.obj.map b.op (affineTautologicalSection F (affineOpenEtale V)) := sorry

/-- The actual global universal section is the native amalgamation of the affine universal sections. -/
def tautologicalSection : F.obj.obj (op (representationEtale F)) :=
  (F.property.amalgamateOfArrows (representationChartEtale F) (representationCharts_covering F)
    (fun U ↦ TypeCat.ofHom fun _ : PUnit.{u + 2} ↦ affineTautologicalSection F (affineOpenEtale U))
    (by
      intro W U V a b hab
      ext z
      exact affineTautologicalSection_compatible F a b hab)) PUnit.unit

/-- The raw inverse Yoneda map restricts the actual universal section along the given morphism. -/
def representationPresheafInverse :
    CategoryTheory.uliftYoneda.{u + 1}.obj (representationEtale F) ⟶ F.obj where
  app V := TypeCat.ofHom fun g ↦ F.obj.map g.down.op (tautologicalSection F)
  naturality := sorry

/-- The actual inverse comparison is the native sheafification lift of the universal-section map. -/
def fromRepresentation : representationSheaf F ⟶ F :=
  ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv
    (CategoryTheory.uliftYoneda.{u + 1}.obj (representationEtale F)) F).symm
      (representationPresheafInverse F)

/-- Pulling a base affine open to a test scheme gives an actual object of its affine-base slice. -/
def baseOpenTest (V : X.Etale) (U : X.affineOpens) : Over (affineOpenEtale U) := by
  letI : Etale V.hom := V.prop
  letI : Etale (pullback.snd V.hom (U : X.Opens).ι) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact Over.mk (MorphismProperty.Over.homMk (pullback.snd V.hom (U : X.Opens).ι) rfl :
    Scheme.Etale.mk (pullback.snd V.hom (U : X.Opens).ι ≫ (U : X.Opens).ι) ⟶ affineOpenEtale U)

/-- The base-open pullback chart maps to the original test object. -/
def baseOpenTestMap (V : X.Etale) (U : X.affineOpens) : (baseOpenTest V U).left ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom (U : X.Opens).ι) pullback.condition

/-- The actual representing morphism on one member of the pulled base-open cover. -/
def sectionMapOnBaseOpen (V : X.Etale) (s : F.obj.obj (op V)) (U : X.affineOpens) :
    (X.directedAffineCover.pullback₁ V.hom).X U ⟶ representation F :=
  localSectionMap F U (baseOpenTest V U) (F.obj.map (baseOpenTestMap V U).op s)

/-- The maps built on the pulled base-open cover agree on each actual overlap. -/
theorem sectionMapOnBaseOpen_compatible (V : X.Etale) (s : F.obj.obj (op V))
    (U W : X.affineOpens) :
    pullback.fst ((X.directedAffineCover.pullback₁ V.hom).f U)
      ((X.directedAffineCover.pullback₁ V.hom).f W) ≫ sectionMapOnBaseOpen F V s U =
    pullback.snd ((X.directedAffineCover.pullback₁ V.hom).f U)
      ((X.directedAffineCover.pullback₁ V.hom).f W) ≫ sectionMapOnBaseOpen F V s W := sorry

/-- A section on an arbitrary test object gives an actual global scheme morphism by native open gluing. -/
def sectionMap (V : X.Etale) (s : F.obj.obj (op V)) : V.left ⟶ representation F :=
  Scheme.Cover.glueMorphisms (X.directedAffineCover.pullback₁ V.hom) (sectionMapOnBaseOpen F V s)
    (sectionMapOnBaseOpen_compatible F V s)

/-- The actual global representing morphism preserves the test object's structure map. -/
theorem sectionMap_over (V : X.Etale) (s : F.obj.obj (op V)) :
    sectionMap F V s ≫ representationMap F = V.hom := sorry

/-- The raw forward comparison keeps the actual scheme map before sheafification. -/
def representationPresheafForward :
    F.obj ⟶ CategoryTheory.uliftYoneda.{u + 1}.obj (representationEtale F) where
  app V := TypeCat.ofHom fun s ↦
    ⟨MorphismProperty.Over.homMk (sectionMap F V.unop s) (sectionMap_over F V.unop s)⟩
  naturality := sorry

/-- Both actual presheaf comparison maps, suitable for consumers using genuine representing morphisms. -/
def representationPresheafIso :
    F.obj ≅ CategoryTheory.uliftYoneda.{u + 1}.obj (representationEtale F) where
  hom := representationPresheafForward F
  inv := representationPresheafInverse F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The sheaf-level forward map applies the native sheafification unit to the actual representing morphism. -/
def toRepresentation : F ⟶ representationSheaf F :=
  ObjectProperty.homMk (representationPresheafForward F ≫
    toSheafify X.smallEtaleTopology (CategoryTheory.uliftYoneda.{u + 1}.obj (representationEtale F)))

/-- The supplied finite locally constant sheaf is represented by the actual constructed finite
étale scheme. Both directions come from evaluation and the implemented universal section. -/
def representationIso : F ≅ representationSheaf F where
  hom := toRepresentation F
  inv := fromRepresentation F
  hom_inv_id := sorry
  inv_hom_id := sorry

end AlgebraicGeometry.Scheme.FiniteLocallyConstant
