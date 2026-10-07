module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap66.Lemma_66_27_2_Ambient

/-! # Canonical comparison with localization at the actual sheaf parameter

The comparison map is obtained by applying the constructed ambient mate to the
graph of a slice object. Its two projections are specified before the pullback
universal property is used to construct the comparison isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Relocalization

variable {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]
variable (hcomm : p ≫ f = g ≫ q)

/-- The first projection of the comparison: apply the ambient mate to the graph
of the given object over `h_V`, then project to the inverse image of its domain. -/
def comparisonLeft (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    ((slicePresentation p g f q hcomm).obj H).left ⟶
      (morphismOfTopoi f).inverseImage.obj H.left :=
  ((slicePresentation p g f q hcomm).map
      ((Over.forgetAdjStar (etaleRepresentable (smallEtaleSite.mk q))).unit.app H)).left ≫
    ((sliceAmbientComparison p g f q hcomm).app H.left).left ≫ prod.snd

/-- The constructed ambient mate sends the graph of a slice object over `h_V`
to the fibre over exactly the Lan/Yoneda parameter of the original square.
On representable sections this is the triangle of `spacesEtalePullbackLift`;
the two adjunction mates transport the same Lan unit used in `Parameter_spec`. -/
theorem comparisonLeft_comm (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    comparisonLeft p g f q hcomm H ≫ (morphismOfTopoi f).inverseImage.map H.hom =
      ((slicePresentation p g f q hcomm).obj H).hom ≫ etaleRelocalizeParameter p g f q hcomm :=
  sorry

/-- The graph square is cartesian. Indeed a slice object is the pullback of its
graph along the diagonal; localization preserves that finite limit, and the
ambient mate carries the diagonal to `etaleRelocalizeParameter`.
The cone's two maps are fixed by `comparisonLeft` and the original slice projection. -/
theorem comparisonSquare (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    IsPullback (comparisonLeft p g f q hcomm H)
      ((slicePresentation p g f q hcomm).obj H).hom
      ((morphismOfTopoi f).inverseImage.map H.hom) (etaleRelocalizeParameter p g f q hcomm) :=
  sorry

/-- The unique comparison to the specified pullback cone, over `h_U`.
Its inverse is the universal lift into the already specified cartesian cone;
no isomorphism is selected from a bare existence claim. -/
def comparisonObjIso (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    (slicePresentation p g f q hcomm).obj H ≅
      (etaleRelocalizeSliceInverseImage p g f q hcomm).obj H :=
  Over.isoMk (comparisonSquare p g f q hcomm H).isoPullback
    (comparisonSquare p g f q hcomm H).isoPullback_hom_snd

/-- The first pullback projection of the comparison is the ambient-mate construction. -/
theorem comparisonObjIso_hom_fst (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    (comparisonObjIso p g f q hcomm H).hom.left ≫
        pullback.fst ((morphismOfTopoi f).inverseImage.map H.hom)
          (etaleRelocalizeParameter p g f q hcomm) = comparisonLeft p g f q hcomm H :=
  (comparisonSquare p g f q hcomm H).isoPullback_hom_fst

/-- The second pullback projection of the comparison is the existing slice structure map. -/
theorem comparisonObjIso_hom_snd (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    (comparisonObjIso p g f q hcomm H).hom.left ≫
        pullback.snd ((morphismOfTopoi f).inverseImage.map H.hom)
          (etaleRelocalizeParameter p g f q hcomm) =
      ((slicePresentation p g f q hcomm).obj H).hom :=
  (comparisonSquare p g f q hcomm H).isoPullback_hom_snd

/-- The actual natural comparison with the inverse-image functor of 18.22.3 at `s`. -/
def parameterInverseImageIso :
    slicePresentation p g f q hcomm ≅ etaleRelocalizeSliceInverseImage p g f q hcomm :=
  NatIso.ofComponents (comparisonObjIso p g f q hcomm) sorry

/-- The 18.22.3 inverse image presented back on the original small site slices. -/
def parameterSiteInverseImage :
    Sheaf ((smallEtaleTopology Y).over (smallEtaleSite.mk q)) (Type u) ⥤
      Sheaf ((smallEtaleTopology X).over (smallEtaleSite.mk p)) (Type u) :=
  (etaleSliceEquivalence Y (smallEtaleSite.mk q)).functor ⋙
    etaleRelocalizeSliceInverseImage p g f q hcomm ⋙
      (etaleSliceEquivalence X (smallEtaleSite.mk p)).inverse

/-- The old inverse image is transported to the actual parameter inverse image,
using the two specified representable equivalences and the pullback comparison. -/
def parameterSiteInverseImageIso :
    (etaleRelocalizeLocalization p g f q hcomm).toTopos.inverseImage ≅
      parameterSiteInverseImage p g f q hcomm :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (etaleSliceEquivalence Y (smallEtaleSite.mk q)).unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleSliceEquivalence Y (smallEtaleSite.mk q)).functor
      ((Functor.rightUnitor _).symm ≪≫
        Functor.isoWhiskerLeft
          ((etaleSliceEquivalence Y (smallEtaleSite.mk q)).inverse ⋙
            (etaleRelocalizeLocalization p g f q hcomm).toTopos.inverseImage)
          (etaleSliceEquivalence X (smallEtaleSite.mk p)).unitIso ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (parameterInverseImageIso p g f q hcomm)
          (etaleSliceEquivalence X (smallEtaleSite.mk p)).inverse)

end AlgebraicGeometry.AlgebraicSpace.Relocalization
