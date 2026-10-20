module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ConstantFiniteRepresentation

/-!
# Affine representation compared with its supplied finite constant charts

The actual intrinsic function-ring coordinates identify an affine representation on a
constant chart with its finite product spectrum. Native base-change pullbacks lift a map
to the descended representation into each of these explicit local models.
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

/-- The actual affine representation regarded as an étale object over the original scheme. -/
def affineRepresentationEtale (U : X.Etale) [IsAffine U.left] : X.Etale :=
  Scheme.Etale.mk (affineRepresentationMap F U ≫ U.hom)

instance affineRepresentationEtale_isAffine (U : X.Etale) [IsAffine U.left] :
    IsAffine (affineRepresentationEtale F U).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (affineAlgebra (F := F) U))))

/-- The actual structural map of the affine representation in the small étale site. -/
def affineRepresentationToBase (U : X.Etale) [IsAffine U.left] :
    affineRepresentationEtale F U ⟶ U :=
  MorphismProperty.Over.homMk (affineRepresentationMap F U) rfl

/-- On a specified constant chart the representing spectrum is the actual product spectrum. -/
def affineConstantCoordinatesIso (U : X.Etale) [IsAffine U.left]
    (E : Type (u + 1)) [Finite E]
    (e : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E) :
    affineRepresentation F U ≅ Spec (CommRingCat.of (chartAlgebra U E)) :=
  Scheme.Spec.mapIso
    (((affineFunctionEquiv F U).trans (localCoordinates F U E e)).symm.toCommRingCatIso.op)

/-- The coordinate isomorphism respects the actual finite product structural map. -/
theorem affineConstantCoordinatesIso_over (U : X.Etale) [IsAffine U.left]
    (E : Type (u + 1)) [Finite E]
    (e : F.over U ≅ (constantSheaf (X.smallEtaleTopology.over U) (Type (u + 1))).obj E) :
    (affineConstantCoordinatesIso F U E e).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) (chartAlgebra U E))) ≫ U.left.isoSpec.inv =
      affineRepresentationMap F U := sorry

variable {U V : X.Etale} [IsAffine U.left] (f : V ⟶ U)
variable (h : V.left ⟶ affineRepresentation F U)

/-- Native actual affine base change lifts the supplied representing morphism on each pulled chart. -/
def pulledRepresentationLift (hf : h ≫ affineRepresentationMap F U = f.left)
    (i : finiteAffineIndex F U) :
    (pullback f (selectedChartMap F U i)).left ⟶ affineRepresentation F (selectedChart F U i) :=
  (affineRestriction_isPullback F (selectedChartMap F U i)).lift
    ((pullback.fst f (selectedChartMap F U i)).left ≫ h)
    (pullback.snd f (selectedChartMap F U i)).left (by
      rw [Category.assoc, hf]
      exact congrArg (fun k : pullback f (selectedChartMap F U i) ⟶ U ↦ k.left)
        (pullback.condition (f := f) (g := selectedChartMap F U i)))

/-- The supplied representing morphism expressed in the explicit finite product chart spectrum. -/
def pulledProductMap (hf : h ≫ affineRepresentationMap F U = f.left)
    (i : finiteAffineIndex F U) :
    (pullback f (selectedChartMap F U i)).left ⟶
      Spec (CommRingCat.of (chartAlgebra (selectedChart F U i) (selectedLabels F U i))) :=
  pulledRepresentationLift F f h hf i ≫
    (affineConstantCoordinatesIso F (selectedChart F U i) (selectedLabels F U i)
      (finiteAffineChartIso F U i)).hom

/-- The actual product-chart morphism lies over the corresponding selected base chart. -/
theorem pulledProductMap_over (hf : h ≫ affineRepresentationMap F U = f.left)
    (i : finiteAffineIndex F U) :
    pulledProductMap F f h hf i ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ((selectedChart F U i).left, ⊤)
        (chartAlgebra (selectedChart F U i) (selectedLabels F U i)))) ≫
          (selectedChart F U i).left.isoSpec.inv =
      (pullback.snd f (selectedChartMap F U i)).left := sorry

/-- The actual local product morphism in the selected chart's slice site. -/
def pulledProductArrow (hf : h ≫ affineRepresentationMap F U = f.left)
    (i : finiteAffineIndex F U) :
    Over.mk (pullback.snd f (selectedChartMap F U i)) ⟶
      Scheme.Etale.ConstantFiniteRepresentation.object (selectedChart F U i) (selectedLabels F U i) :=
  Over.homMk (MorphismProperty.Over.homMk (pulledProductMap F f h hf i) (by
    change pulledProductMap F f h hf i ≫
      (Scheme.Etale.ConstantFiniteRepresentation.structureMap (selectedChart F U i) (selectedLabels F U i) ≫
        (selectedChart F U i).hom) = (pullback f (selectedChartMap F U i)).hom
    rw [← Category.assoc]
    change (pulledProductMap F f h hf i ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ((selectedChart F U i).left, ⊤)
        (chartAlgebra (selectedChart F U i) (selectedLabels F U i)))) ≫
          (selectedChart F U i).left.isoSpec.inv) ≫ (selectedChart F U i).hom = _
    rw [pulledProductMap_over]
    exact MorphismProperty.Over.w (pullback.snd f (selectedChartMap F U i)))) (by
      apply MorphismProperty.Over.Hom.ext
      exact pulledProductMap_over F f h hf i)

/-- The real inverse of the finite constant model produces a section on each pulled chart. -/
def pulledChartSection (hf : h ≫ affineRepresentationMap F U = f.left)
    (i : finiteAffineIndex F U) : F.obj.obj (op (pullback f (selectedChartMap F U i))) :=
  (finiteAffineChartIso F U i).inv.hom.app (op (Over.mk (pullback.snd f (selectedChartMap F U i))))
    ((Scheme.Etale.ConstantFiniteRepresentation.iso (selectedChart F U i)
      (labelEquiv (selectedLabels F U i))).inv.hom.app
        (op (Over.mk (pullback.snd f (selectedChartMap F U i))))
      ((toSheafify (X.smallEtaleTopology.over (selectedChart F U i))
        (CategoryTheory.uliftYoneda.{u + 1}.obj
          (Scheme.Etale.ConstantFiniteRepresentation.object (selectedChart F U i) (selectedLabels F U i)))).app
            (op (Over.mk (pullback.snd f (selectedChartMap F U i))))
        ⟨pulledProductArrow F f h hf i⟩))

/-- The fixed finite affine cover pulls back to a real covering sieve on any test object. -/
theorem pulledCharts_covering :
    Sieve.ofArrows (fun i : finiteAffineIndex F U ↦ pullback f (selectedChartMap F U i))
      (fun i ↦ pullback.fst f (selectedChartMap F U i)) ∈ X.smallEtaleTopology V := by
  rw [Sieve.ofArrows_eq_pullback_of_isPullback (selectedChartMap F U)
    (fun i ↦ IsPullback.of_hasPullback f (selectedChartMap F U i))]
  apply X.smallEtaleTopology.pullback_stable f
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff (selectedChartMap F U)).mpr
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, y, hy⟩ := (finiteAffineCover F U).cover x
  exact Set.mem_iUnion.mpr ⟨i, y, hy⟩

/-- The local sections agree on every common test mapping into two pulled charts. -/
theorem pulledChartSection_compatible (hf : h ≫ affineRepresentationMap F U = f.left)
    {W : X.Etale} {i j : finiteAffineIndex F U}
    (a : W ⟶ pullback f (selectedChartMap F U i))
    (b : W ⟶ pullback f (selectedChartMap F U j))
    (hab : a ≫ pullback.fst f (selectedChartMap F U i) =
      b ≫ pullback.fst f (selectedChartMap F U j)) :
    F.obj.map a.op (pulledChartSection F f h hf i) =
      F.obj.map b.op (pulledChartSection F f h hf j) := sorry

/-- The actual affine inverse glues the sections returned by the supplied finite constant models. -/
def affineMapSection (hf : h ≫ affineRepresentationMap F U = f.left) : F.obj.obj (op V) :=
  (F.property.amalgamateOfArrows
    (fun i : finiteAffineIndex F U ↦ pullback.fst f (selectedChartMap F U i))
    (pulledCharts_covering F f)
    (fun i ↦ TypeCat.ofHom fun _ : PUnit.{u + 2} ↦ pulledChartSection F f h hf i)
    (by
      intro W i j a b hab
      ext z
      exact pulledChartSection_compatible F f h hf a b hab)) PUnit.unit

/-- The universal section of the affine representation comes from its actual identity morphism. -/
def affineTautologicalSection (W : X.Etale) [IsAffine W.left] :
    F.obj.obj (op (affineRepresentationEtale F W)) :=
  affineMapSection F (affineRepresentationToBase F W) (𝟙 _) (Category.id_comp _)

end AlgebraicGeometry.Scheme.FiniteLocallyConstant
