/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Sites.LeftExact
public import stacks_project.Chap103.Remark_103_10_6_Sheafification
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf

/-!
# Fppf and étale sheafification for categories fibred in groupoids

The finite-type affine charts form a small local basis containing the identity
object. Both topology comparisons and the resulting original-universe
sheafification certificates are proved, without additional size assumptions.
-/

/-! ## FiniteTypeAffineCharts -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MorphismProperty
universe u

namespace AlgebraicGeometry.GroupoidsOver.Sheafification

abbrev fppfProperty : MorphismProperty Scheme.{u} :=
  @Flat ⊓ @LocallyOfFinitePresentation

instance : fppfProperty.{u}.IsMultiplicative where
  id_mem X := ⟨inferInstance, inferInstance⟩
  comp_mem f g hf hg := by
    -- Local instance justification (proof-local temporary data): use the given morphism-property hypothesis to derive its finite-type or composite property.
    letI := hf.1
    -- Local instance justification (proof-local temporary data): use the given morphism-property hypothesis to derive its finite-type or composite property.
    letI := hf.2
    -- Local instance justification (proof-local temporary data): use the given morphism-property hypothesis to derive its finite-type or composite property.
    letI := hg.1
    -- Local instance justification (proof-local temporary data): use the given morphism-property hypothesis to derive its finite-type or composite property.
    letI := hg.2
    exact ⟨inferInstance, inferInstance⟩

/-- The actual affine schemes locally of finite type over a fixed scheme. -/
abbrev AffineFiniteType (S : Scheme.{u}) :=
  MorphismProperty.CostructuredArrow @LocallyOfFiniteType.{u} ⊤ Scheme.Spec.{u} S

/-- Finite-type algebra presentations give a genuine small model for this local site. -/
instance (S : Scheme.{u}) : EssentiallySmall.{u} (AffineFiniteType S) :=
  essentiallySmall_costructuredArrow_Spec _ le_rfl


end AlgebraicGeometry.GroupoidsOver.Sheafification

end

/-! ## RelativeFppfBasis -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MorphismProperty CategoryTheory.Limits
universe u

namespace AlgebraicGeometry.GroupoidsOver.Sheafification

instance : MorphismProperty.HasOfPostcompProperty @LocallyOfFiniteType.{u} @LocallyOfFiniteType.{u} where
  of_postcomp f g hg hfg := by
    -- Local instance justification (proof-local temporary data): use the given morphism-property hypothesis to derive its finite-type or composite property.
    letI := hfg
    exact locallyOfFiniteType_of_comp f g

/-- Locally finite-type test schemes over a fixed object, with the fppf topology. -/
abbrev RelativeFiniteType (S : Scheme.{u}) := MorphismProperty.Over @LocallyOfFiniteType.{u} ⊤ S

def relativeInclusion (S : Scheme.{u}) : RelativeFiniteType S ⥤ Over S :=
  MorphismProperty.Over.forget @LocallyOfFiniteType ⊤ S

abbrev relativeTopology (S : Scheme.{u}) : GrothendieckTopology (RelativeFiniteType S) :=
  (relativeInclusion S).restrictedTopology (Scheme.fppfTopology.over S)

instance (S : Scheme.{u}) : (relativeInclusion S).Full :=
  inferInstanceAs (MorphismProperty.Over.forget @LocallyOfFiniteType ⊤ S).Full
instance (S : Scheme.{u}) : (relativeInclusion S).Faithful :=
  inferInstanceAs (MorphismProperty.Over.forget @LocallyOfFiniteType ⊤ S).Faithful

/-- Fppf covers of a finite-type test object remain finite-type over its base. -/
instance (S : Scheme.{u}) : (relativeInclusion S).LocallyCoverDense (Scheme.fppfTopology.over S) :=
  Scheme.locallyCoverDense_of_le S (by
    intro U V f hf
    -- Local instance justification (proof-local temporary data): use the given morphism-property hypothesis to derive its finite-type or composite property.
    letI := hf.2
    infer_instance)

/-- The inclusion retains the same covering sieves, so it is cocontinuous. -/
instance (S : Scheme.{u}) : (relativeInclusion S).IsCocontinuous
    (relativeTopology S) (Scheme.fppfTopology.over S) := by
  dsimp only [relativeTopology]
  infer_instance

/-- The finite-type inclusion preserves finite limits and covering sieves. -/
instance (S : Scheme.{u}) : (relativeInclusion S).IsContinuous
    (relativeTopology S) (Scheme.fppfTopology.over S) := by
  -- Local instance justification (defeq pin): expose this inclusion as the standard finite-type forgetful functor for finite-limit inference.
  letI : PreservesFiniteLimits (relativeInclusion S) := by
    dsimp only [relativeInclusion]
    infer_instance
  -- Local instance justification (proof-local temporary data): use the finite limits just constructed to certify this exact inclusion as flat.
  letI := flat_of_preservesFiniteLimits (relativeInclusion S)
  apply Functor.isContinuous_iff_coverPreserving.mpr
  exact (relativeInclusion S).coverPreserving_restrictedTopology _

def affineFiniteInclusion (S : Scheme.{u}) : AffineFiniteType S ⥤ RelativeFiniteType S :=
  MorphismProperty.CostructuredArrow.toOver _ _ _

instance (S : Scheme.{u}) : (affineFiniteInclusion S).Full :=
  inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).Full
instance (S : Scheme.{u}) : (affineFiniteInclusion S).Faithful :=
  inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).Faithful

set_option backward.isDefEq.respectTransparency false in
/-- Affine open charts are fppf covers inside the finite-type relative site. -/
instance (S : Scheme.{u}) : (affineFiniteInclusion S).IsCoverDense (relativeTopology S) where
  is_cover U := by
    apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    apply (Scheme.mem_overGrothendieckTopology fppfProperty _ _).mpr
    let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage fppfProperty) U.left :=
      U.left.affineCover.changeProp (fun f => ⟨inferInstance, inferInstance⟩)
    -- Local instance justification (defeq pin): equip each affine chart with its literal composite structure morphism to S.
    letI (i : 𝒰.I₀) : (𝒰.X i).Over S := ⟨𝒰.f i ≫ U.hom⟩
    let hOver : 𝒰.Over S := { over := fun i => inferInstance, isOver_map := fun i => ⟨rfl⟩ }
    refine ⟨𝒰, hOver, ?_⟩
    rintro V f ⟨i⟩
    -- Local instance justification (proof-local temporary data): these are the actual structure and cover arrows, with properties supplied by the chosen chart.
    letI : LocallyOfFiniteType U.hom := U.prop
    -- Local instance justification (proof-local temporary data): these are the actual structure and cover arrows, with properties supplied by the chosen chart.
    letI : LocallyOfFinitePresentation (𝒰.f i) := (𝒰.map_prop i).2
    let A : AffineFiniteType S := Scheme.affineOverMk (𝒰.f i ≫ U.hom) inferInstance
    let g : (affineFiniteInclusion S).obj A ⟶ U :=
      MorphismProperty.Over.homMk (𝒰.f i) rfl trivial
    refine ⟨(affineFiniteInclusion S).obj A, g, 𝟙 _, ?_, ?_⟩
    · exact ⟨⟨A, 𝟙 _, g, Category.id_comp g⟩⟩
    · ext
      exact (Category.id_comp _).symm

def smallAffineFiniteInclusion (S : Scheme.{u}) :
    SmallModel.{u} (AffineFiniteType S) ⥤ RelativeFiniteType S :=
  (equivSmallModel (AffineFiniteType S)).inverse ⋙ affineFiniteInclusion S

instance (S : Scheme.{u}) : (smallAffineFiniteInclusion S).IsCoverDense (relativeTopology S) :=
  coverDense_precomp_equivalence (equivSmallModel (AffineFiniteType S)).symm
    (affineFiniteInclusion S) (relativeTopology S)

def relativeIdentity (S : Scheme.{u}) : RelativeFiniteType S :=
  ⟨Over.mk (𝟙 S), (inferInstance : LocallyOfFiniteType (𝟙 S))⟩

abbrev RelativeBasis (S : Scheme.{u}) :=
  PointedBasis (smallAffineFiniteInclusion S) (relativeIdentity S)

def relativeBasisInclusion (S : Scheme.{u}) : RelativeBasis S ⥤ RelativeFiniteType S :=
  pointedInclusion (smallAffineFiniteInclusion S) (relativeIdentity S)

instance (S : Scheme.{u}) : (relativeBasisInclusion S).Full := (fullyFaithfulInducedFunctor _).full
instance (S : Scheme.{u}) : (relativeBasisInclusion S).Faithful := (fullyFaithfulInducedFunctor _).faithful
instance (S : Scheme.{u}) : (relativeBasisInclusion S).IsCoverDense (relativeTopology S) :=
  pointedCoverDense _ _ _

def relativeBasisTopology (S : Scheme.{u}) :=
  (relativeBasisInclusion S).inducedTopology (relativeTopology S)

instance (S : Scheme.{u}) : (relativeBasisInclusion S).IsDenseSubsite
    (relativeBasisTopology S) (relativeTopology S) := by
  dsimp only [relativeBasisTopology]
  infer_instance

/-- A u-small local site whose inclusion reaches the identity object of `Over S`
literally, so the local size theorem applies at that exact object. -/
def smallLocalToOver (S : Scheme.{u}) : RelativeBasis S ⥤ Over S :=
  relativeBasisInclusion S ⋙ relativeInclusion S

instance (S : Scheme.{u}) : (smallLocalToOver S).IsContinuous
    (relativeBasisTopology S) (Scheme.fppfTopology.over S) :=
  Functor.isContinuous_comp _ _ _ (relativeTopology S) _

instance (S : Scheme.{u}) : (smallLocalToOver S).IsCocontinuous
    (relativeBasisTopology S) (Scheme.fppfTopology.over S) := by
  dsimp only [smallLocalToOver]
  exact isCocontinuous_comp (relativeBasisInclusion S) (relativeInclusion S)
    (relativeBasisTopology S) (relativeTopology S)

end AlgebraicGeometry.GroupoidsOver.Sheafification

end

/-! ## RelativeEtaleBasis -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.MorphismProperty CategoryTheory.Limits
universe u

namespace AlgebraicGeometry.GroupoidsOver.Sheafification.Etale

instance : MorphismProperty.HasOfPostcompProperty @LocallyOfFiniteType.{u} @LocallyOfFiniteType.{u} where
  of_postcomp f g hg hfg := by
    -- Local instance justification (proof-local temporary data): use the given morphism-property hypothesis to derive its finite-type or composite property.
    letI := hfg
    exact locallyOfFiniteType_of_comp f g

/-- Locally finite-type test schemes over a fixed object, with the étale topology. -/
abbrev RelativeFiniteType (S : Scheme.{u}) := MorphismProperty.Over @LocallyOfFiniteType.{u} ⊤ S

def relativeInclusion (S : Scheme.{u}) : RelativeFiniteType S ⥤ Over S :=
  MorphismProperty.Over.forget @LocallyOfFiniteType ⊤ S

abbrev relativeTopology (S : Scheme.{u}) : GrothendieckTopology (RelativeFiniteType S) :=
  (relativeInclusion S).restrictedTopology (Scheme.etaleTopology.over S)

instance (S : Scheme.{u}) : (relativeInclusion S).Full :=
  inferInstanceAs (MorphismProperty.Over.forget @LocallyOfFiniteType ⊤ S).Full
instance (S : Scheme.{u}) : (relativeInclusion S).Faithful :=
  inferInstanceAs (MorphismProperty.Over.forget @LocallyOfFiniteType ⊤ S).Faithful

/-- Étale covers of a finite-type test object remain finite-type over its base. -/
instance (S : Scheme.{u}) : (relativeInclusion S).LocallyCoverDense (Scheme.etaleTopology.over S) :=
  Scheme.locallyCoverDense_of_le S (by
    intro U V f hf
    -- Local instance justification (proof-local temporary data): use the given morphism-property hypothesis to derive its finite-type or composite property.
    letI := hf
    infer_instance)

/-- The inclusion retains the same covering sieves, so it is cocontinuous. -/
instance (S : Scheme.{u}) : (relativeInclusion S).IsCocontinuous
    (relativeTopology S) (Scheme.etaleTopology.over S) := by
  dsimp only [relativeTopology]
  infer_instance

/-- The finite-type inclusion preserves finite limits and covering sieves. -/
instance (S : Scheme.{u}) : (relativeInclusion S).IsContinuous
    (relativeTopology S) (Scheme.etaleTopology.over S) := by
  -- Local instance justification (defeq pin): expose this inclusion as the standard finite-type forgetful functor for finite-limit inference.
  letI : PreservesFiniteLimits (relativeInclusion S) := by
    dsimp only [relativeInclusion]
    infer_instance
  -- Local instance justification (proof-local temporary data): use the finite limits just constructed to certify this exact inclusion as flat.
  letI := flat_of_preservesFiniteLimits (relativeInclusion S)
  apply Functor.isContinuous_iff_coverPreserving.mpr
  exact (relativeInclusion S).coverPreserving_restrictedTopology _

def affineFiniteInclusion (S : Scheme.{u}) : AffineFiniteType S ⥤ RelativeFiniteType S :=
  MorphismProperty.CostructuredArrow.toOver _ _ _

instance (S : Scheme.{u}) : (affineFiniteInclusion S).Full :=
  inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).Full
instance (S : Scheme.{u}) : (affineFiniteInclusion S).Faithful :=
  inferInstanceAs (MorphismProperty.CostructuredArrow.toOver _ _ _).Faithful

set_option backward.isDefEq.respectTransparency false in
/-- Affine open charts are étale covers inside the finite-type relative site. -/
instance (S : Scheme.{u}) : (affineFiniteInclusion S).IsCoverDense (relativeTopology S) where
  is_cover U := by
    apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    apply (Scheme.mem_overGrothendieckTopology (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) _ _).mpr
    let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})) U.left :=
      U.left.affineCover.changeProp (fun f => inferInstance)
    -- Local instance justification (defeq pin): equip each affine chart with its literal composite structure morphism to S.
    letI (i : 𝒰.I₀) : (𝒰.X i).Over S := ⟨𝒰.f i ≫ U.hom⟩
    let hOver : 𝒰.Over S := { over := fun i => inferInstance, isOver_map := fun i => ⟨rfl⟩ }
    refine ⟨𝒰, hOver, ?_⟩
    rintro V f ⟨i⟩
    -- Local instance justification (proof-local temporary data): these are the actual structure and cover arrows, with properties supplied by the chosen chart.
    letI : LocallyOfFiniteType U.hom := U.prop
    -- Local instance justification (proof-local temporary data): these are the actual structure and cover arrows, with properties supplied by the chosen chart.
    letI : AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
    let A : AffineFiniteType S := Scheme.affineOverMk (𝒰.f i ≫ U.hom) inferInstance
    let g : (affineFiniteInclusion S).obj A ⟶ U :=
      MorphismProperty.Over.homMk (𝒰.f i) rfl trivial
    refine ⟨(affineFiniteInclusion S).obj A, g, 𝟙 _, ?_, ?_⟩
    · exact ⟨⟨A, 𝟙 _, g, Category.id_comp g⟩⟩
    · ext
      exact (Category.id_comp _).symm

def smallAffineFiniteInclusion (S : Scheme.{u}) :
    SmallModel.{u} (AffineFiniteType S) ⥤ RelativeFiniteType S :=
  (equivSmallModel (AffineFiniteType S)).inverse ⋙ affineFiniteInclusion S

instance (S : Scheme.{u}) : (smallAffineFiniteInclusion S).IsCoverDense (relativeTopology S) :=
  coverDense_precomp_equivalence (equivSmallModel (AffineFiniteType S)).symm
    (affineFiniteInclusion S) (relativeTopology S)

def relativeIdentity (S : Scheme.{u}) : RelativeFiniteType S :=
  ⟨Over.mk (𝟙 S), (inferInstance : LocallyOfFiniteType (𝟙 S))⟩

abbrev RelativeBasis (S : Scheme.{u}) :=
  PointedBasis (smallAffineFiniteInclusion S) (relativeIdentity S)

def relativeBasisInclusion (S : Scheme.{u}) : RelativeBasis S ⥤ RelativeFiniteType S :=
  pointedInclusion (smallAffineFiniteInclusion S) (relativeIdentity S)

instance (S : Scheme.{u}) : (relativeBasisInclusion S).Full := (fullyFaithfulInducedFunctor _).full
instance (S : Scheme.{u}) : (relativeBasisInclusion S).Faithful := (fullyFaithfulInducedFunctor _).faithful
instance (S : Scheme.{u}) : (relativeBasisInclusion S).IsCoverDense (relativeTopology S) :=
  pointedCoverDense _ _ _

def relativeBasisTopology (S : Scheme.{u}) :=
  (relativeBasisInclusion S).inducedTopology (relativeTopology S)

instance (S : Scheme.{u}) : (relativeBasisInclusion S).IsDenseSubsite
    (relativeBasisTopology S) (relativeTopology S) := by
  dsimp only [relativeBasisTopology]
  infer_instance

/-- A u-small local site whose inclusion reaches the identity object of `Over S`
literally, so the local size theorem applies at that exact object. -/
def smallLocalToOver (S : Scheme.{u}) : RelativeBasis S ⥤ Over S :=
  relativeBasisInclusion S ⋙ relativeInclusion S

instance (S : Scheme.{u}) : (smallLocalToOver S).IsContinuous
    (relativeBasisTopology S) (Scheme.etaleTopology.over S) :=
  Functor.isContinuous_comp _ _ _ (relativeTopology S) _

instance (S : Scheme.{u}) : (smallLocalToOver S).IsCocontinuous
    (relativeBasisTopology S) (Scheme.etaleTopology.over S) := by
  dsimp only [smallLocalToOver]
  exact isCocontinuous_comp (relativeBasisInclusion S) (relativeInclusion S)
    (relativeBasisTopology S) (relativeTopology S)

end AlgebraicGeometry.GroupoidsOver.Sheafification.Etale

end

/-! ## UpperCertificate -/

@[expose] public section
open AlgebraicGeometry CategoryTheory AlgebraicGeometry.GroupoidsOver
universe u

/-- Mathlib's plus construction provides a proved certificate in the size of
the total category. This does not assert the needed universe-u certificate. -/
theorem AlgebraicGeometry.GroupoidsOver.Sheafification.certifiedUpperFppf {S : Scheme.{u}} (X : GroupoidsOver S) :
    HasSheafify (inheritedFppfTopology X) AddCommGrpCat.{u + 1} := by
  infer_instance

end

/-! ## StackFppfCertificate -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidsOver Opposite
universe u
namespace AlgebraicGeometry.GroupoidsOver.Sheafification
variable {S : Scheme.{u}} (X : GroupoidsOver S) (x : X.total)

-- Local instance justification (instance diamond): pin the proved upper-universe plus-construction certificate instead of the imported admitted witness.
local instance certifiedWeakUpper : HasWeakSheafify (inheritedFppfTopology X) AddCommGrpCat.{u + 1} :=
  (certifiedUpperFppf X).isRightAdjoint

def stackSliceEquiv : Over x ≌ Over (X.p.obj x) := by
  -- Local instance justification (instance diamond): select the proved slice equivalence instead of the imported admitted overPost instance.
  letI := fiberSliceIsEquivalence X.p x
  exact (Over.post X.p).asEquivalence

instance : (stackSliceEquiv X x).functor.IsDenseSubsite
    ((inheritedFppfTopology X).over x) ((Scheme.fppfTopology.over S).over (X.p.obj x)) :=
  fiberSliceDense X.p (Scheme.fppfTopology.over S) x

instance : (stackSliceEquiv X x).inverse.IsDenseSubsite
    ((Scheme.fppfTopology.over S).over (X.p.obj x)) ((inheritedFppfTopology X).over x) := by
  let e := stackSliceEquiv X x
  -- Local instance justification (defeq pin): expose the proved forward dense-subsite instance as the inverse of the symmetric slice equivalence.
  letI : e.symm.inverse.IsDenseSubsite ((inheritedFppfTopology X).over x)
      ((Scheme.fppfTopology.over S).over (X.p.obj x)) :=
    fiberSliceDense X.p (Scheme.fppfTopology.over S) x
  have h := e.symm.eq_inducedTopology_of_isDenseSubsite
    ((Scheme.fppfTopology.over S).over (X.p.obj x)) ((inheritedFppfTopology X).over x)
  rw [h]
  change e.symm.functor.IsDenseSubsite _ (e.symm.inverse.inducedTopology _)
  infer_instance

/-- Scheme-local test objects, transported through the actual slice equivalence,
give a small local site on the total groupoid category. -/
def stackLocalToTotal : RelativeBasis (X.p.obj x).left ⥤ X.total :=
  smallLocalToOver (X.p.obj x).left ⋙
    (X.p.obj x).iteratedSliceBackward ⋙
    (stackSliceEquiv X x).inverse ⋙ Over.forget x

instance : (stackLocalToTotal X x).IsContinuous
    (relativeBasisTopology (X.p.obj x).left) (inheritedFppfTopology X) := by
  -- Local instance justification (defeq pin): specify the intermediate slice topology for this exact composition of continuous site functors.
  letI : ((stackSliceEquiv X x).inverse ⋙ Over.forget x).IsContinuous
      ((Scheme.fppfTopology.over S).over (X.p.obj x)) (inheritedFppfTopology X) :=
    Functor.isContinuous_comp _ _ _ ((inheritedFppfTopology X).over x) _
  -- Local instance justification (defeq pin): specify the intermediate slice topology for this exact composition of continuous site functors.
  letI : ((X.p.obj x).iteratedSliceBackward ⋙
      (stackSliceEquiv X x).inverse ⋙ Over.forget x).IsContinuous
      (Scheme.fppfTopology.over (X.p.obj x).left) (inheritedFppfTopology X) :=
    Functor.isContinuous_comp _ _ _ ((Scheme.fppfTopology.over S).over (X.p.obj x)) _
  exact Functor.isContinuous_comp _ _ _ (Scheme.fppfTopology.over (X.p.obj x).left) _

instance : (stackLocalToTotal X x).IsCocontinuous
    (relativeBasisTopology (X.p.obj x).left) (inheritedFppfTopology X) := by
  -- Local instance justification (defeq pin): specify the intermediate slice topology for this exact composition of cover-lifting functors.
  letI : ((stackSliceEquiv X x).inverse ⋙ Over.forget x).IsCocontinuous
      ((Scheme.fppfTopology.over S).over (X.p.obj x)) (inheritedFppfTopology X) :=
    isCocontinuous_comp _ _ _ ((inheritedFppfTopology X).over x)
  -- Local instance justification (defeq pin): specify the intermediate slice topology for this exact composition of cover-lifting functors.
  letI : ((X.p.obj x).iteratedSliceBackward ⋙
      (stackSliceEquiv X x).inverse ⋙ Over.forget x).IsCocontinuous
      (Scheme.fppfTopology.over (X.p.obj x).left) (inheritedFppfTopology X) :=
    isCocontinuous_comp _ _ _ ((Scheme.fppfTopology.over S).over (X.p.obj x))
  exact isCocontinuous_comp _ _ _ (Scheme.fppfTopology.over (X.p.obj x).left)

/-- The distinguished local chart represents the original total-category object. -/
def stackLocalPointIso :
    (stackLocalToTotal X x).obj (none : RelativeBasis (X.p.obj x).left) ≅ x := by
  let e := stackSliceEquiv X x
  let i : ((X.p.obj x).iteratedSliceBackward).obj (Over.mk (𝟙 (X.p.obj x).left)) ≅
      e.functor.obj (Over.mk (𝟙 x)) :=
    Over.isoMk (Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (X.p.obj x).hom = 𝟙 _ ≫ (X.p.obj x).hom
      rfl)) (by
        change (Over.homMk (𝟙 _) (Category.id_comp _)) ≫ X.p.map (𝟙 x) =
          Over.homMk (𝟙 _) (Category.id_comp _)
        rw [X.p.map_id]
        ext
        simp)
  exact (Over.forget x).mapIso (e.inverse.mapIso i ≪≫ (e.unitIso.app (Over.mk (𝟙 x))).symm)

/-- The upper sheafification has genuinely small sections at every object,
using local finite-type charts and proved topological comparisons. -/
theorem stackUpperSectionsSmall (P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u})
    (V : X.totalᵒᵖ) :
    Small.{u} ((sheafify (inheritedFppfTopology X)
      (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})).obj V) := by
  -- Local instance justification (proof-local temporary data): use the proved size of the distinguished local section before transport to this total object.
  letI := sectionSmall (stackLocalToTotal X V.unop)
    (relativeBasisTopology (X.p.obj V.unop).left) (inheritedFppfTopology X)
    P (none : RelativeBasis (X.p.obj V.unop).left)
  let i := (sheafify (inheritedFppfTopology X)
    (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})).mapIso (stackLocalPointIso X V.unop).op
  exact small_of_injective (ConcreteCategory.bijective_of_isIso i.hom).1

/-- A proved unlifted sheafification certificate for the actual inherited
fppf site. No smallness, sheafification, or geometric assumption is added. -/
theorem stackHasWeakSheafify : HasWeakSheafify (inheritedFppfTopology X) AddCommGrpCat.{u} := by
  -- Local instance justification (instance diamond): lower the proved plus-construction adjunction instead of the old admitted upper certificate.
  letI := certifiedUpperFppf X
  exact lowerHasWeakSheafify (inheritedFppfTopology X) (stackUpperSectionsSmall X)

end AlgebraicGeometry.GroupoidsOver.Sheafification

end

/-! ## StackEtaleCertificate -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidsOver Opposite
universe u
namespace AlgebraicGeometry.GroupoidsOver.Sheafification.Etale
variable {S : Scheme.{u}} (X : GroupoidsOver S) (x : X.total)

-- Local instance justification (instance diamond): pin the proved upper-universe plus-construction certificate instead of the imported admitted witness.
local instance certifiedWeakUpper : HasWeakSheafify (X.etaleTopology) AddCommGrpCat.{u + 1} :=
  ((show HasSheafify X.etaleTopology AddCommGrpCat.{u + 1} from inferInstance)).isRightAdjoint

def stackSliceEquiv : Over x ≌ Over (X.p.obj x) := by
  -- Local instance justification (instance diamond): select the proved slice equivalence instead of the imported admitted overPost instance.
  letI := fiberSliceIsEquivalence X.p x
  exact (Over.post X.p).asEquivalence

instance : (stackSliceEquiv X x).functor.IsDenseSubsite
    ((X.etaleTopology).over x) ((Scheme.etaleTopology.over S).over (X.p.obj x)) :=
  fiberSliceDense X.p (Scheme.etaleTopology.over S) x

instance : (stackSliceEquiv X x).inverse.IsDenseSubsite
    ((Scheme.etaleTopology.over S).over (X.p.obj x)) ((X.etaleTopology).over x) := by
  let e := stackSliceEquiv X x
  -- Local instance justification (defeq pin): expose the proved forward dense-subsite instance as the inverse of the symmetric slice equivalence.
  letI : e.symm.inverse.IsDenseSubsite ((X.etaleTopology).over x)
      ((Scheme.etaleTopology.over S).over (X.p.obj x)) :=
    fiberSliceDense X.p (Scheme.etaleTopology.over S) x
  have h := e.symm.eq_inducedTopology_of_isDenseSubsite
    ((Scheme.etaleTopology.over S).over (X.p.obj x)) ((X.etaleTopology).over x)
  rw [h]
  change e.symm.functor.IsDenseSubsite _ (e.symm.inverse.inducedTopology _)
  infer_instance

/-- Scheme-local test objects, transported through the actual slice equivalence,
give a small local site on the total groupoid category. -/
def stackLocalToTotal : RelativeBasis (X.p.obj x).left ⥤ X.total :=
  smallLocalToOver (X.p.obj x).left ⋙
    (X.p.obj x).iteratedSliceBackward ⋙
    (stackSliceEquiv X x).inverse ⋙ Over.forget x

instance : (stackLocalToTotal X x).IsContinuous
    (relativeBasisTopology (X.p.obj x).left) (X.etaleTopology) := by
  -- Local instance justification (defeq pin): specify the intermediate slice topology for this exact composition of continuous site functors.
  letI : ((stackSliceEquiv X x).inverse ⋙ Over.forget x).IsContinuous
      ((Scheme.etaleTopology.over S).over (X.p.obj x)) (X.etaleTopology) :=
    Functor.isContinuous_comp _ _ _ ((X.etaleTopology).over x) _
  -- Local instance justification (defeq pin): specify the intermediate slice topology for this exact composition of continuous site functors.
  letI : ((X.p.obj x).iteratedSliceBackward ⋙
      (stackSliceEquiv X x).inverse ⋙ Over.forget x).IsContinuous
      (Scheme.etaleTopology.over (X.p.obj x).left) (X.etaleTopology) :=
    Functor.isContinuous_comp _ _ _ ((Scheme.etaleTopology.over S).over (X.p.obj x)) _
  exact Functor.isContinuous_comp _ _ _ (Scheme.etaleTopology.over (X.p.obj x).left) _

instance : (stackLocalToTotal X x).IsCocontinuous
    (relativeBasisTopology (X.p.obj x).left) (X.etaleTopology) := by
  -- Local instance justification (defeq pin): specify the intermediate slice topology for this exact composition of cover-lifting functors.
  letI : ((stackSliceEquiv X x).inverse ⋙ Over.forget x).IsCocontinuous
      ((Scheme.etaleTopology.over S).over (X.p.obj x)) (X.etaleTopology) :=
    isCocontinuous_comp _ _ _ ((X.etaleTopology).over x)
  -- Local instance justification (defeq pin): specify the intermediate slice topology for this exact composition of cover-lifting functors.
  letI : ((X.p.obj x).iteratedSliceBackward ⋙
      (stackSliceEquiv X x).inverse ⋙ Over.forget x).IsCocontinuous
      (Scheme.etaleTopology.over (X.p.obj x).left) (X.etaleTopology) :=
    isCocontinuous_comp _ _ _ ((Scheme.etaleTopology.over S).over (X.p.obj x))
  exact isCocontinuous_comp _ _ _ (Scheme.etaleTopology.over (X.p.obj x).left)

/-- The distinguished local chart represents the original total-category object. -/
def stackLocalPointIso :
    (stackLocalToTotal X x).obj (none : RelativeBasis (X.p.obj x).left) ≅ x := by
  let e := stackSliceEquiv X x
  let i : ((X.p.obj x).iteratedSliceBackward).obj (Over.mk (𝟙 (X.p.obj x).left)) ≅
      e.functor.obj (Over.mk (𝟙 x)) :=
    Over.isoMk (Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (X.p.obj x).hom = 𝟙 _ ≫ (X.p.obj x).hom
      rfl)) (by
        change (Over.homMk (𝟙 _) (Category.id_comp _)) ≫ X.p.map (𝟙 x) =
          Over.homMk (𝟙 _) (Category.id_comp _)
        rw [X.p.map_id]
        ext
        simp)
  exact (Over.forget x).mapIso (e.inverse.mapIso i ≪≫ (e.unitIso.app (Over.mk (𝟙 x))).symm)

/-- The upper sheafification has genuinely small sections at every object,
using local finite-type charts and proved topological comparisons. -/
theorem stackUpperSectionsSmall (P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u})
    (V : X.totalᵒᵖ) :
    Small.{u} ((sheafify (X.etaleTopology)
      (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})).obj V) := by
  -- Local instance justification (proof-local temporary data): use the proved size of the distinguished local section before transport to this total object.
  letI := sectionSmall (stackLocalToTotal X V.unop)
    (relativeBasisTopology (X.p.obj V.unop).left) (X.etaleTopology)
    P (none : RelativeBasis (X.p.obj V.unop).left)
  let i := (sheafify (X.etaleTopology)
    (P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})).mapIso (stackLocalPointIso X V.unop).op
  exact small_of_injective (ConcreteCategory.bijective_of_isIso i.hom).1

/-- A proved unlifted sheafification certificate for the actual inherited
étale site. No smallness, sheafification, or geometric assumption is added. -/
theorem stackHasWeakSheafify : HasWeakSheafify (X.etaleTopology) AddCommGrpCat.{u} := by
  -- Local instance justification (instance diamond): lower the proved plus-construction adjunction instead of the old admitted upper certificate.
  letI := (show HasSheafify X.etaleTopology AddCommGrpCat.{u + 1} from inferInstance)
  exact lowerHasWeakSheafify (X.etaleTopology) (stackUpperSectionsSmall X)

end AlgebraicGeometry.GroupoidsOver.Sheafification.Etale

end
