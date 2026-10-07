module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Variety
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

/-!
# Associated cycles and flat pullback for varieties

This file specializes compatibility of associated cycles with flat pullback to the canonical
dimension grading of varieties over a field.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a flat morphism of varieties, flat pullback of the degree-`k` cycle associated to a
coherent module is the degree shifted by the canonical relative-dimension gap of the morphism. -/
theorem associatedCycle_pullback_of_varieties
    {K : Type u} [Field K]
    (X Y : SchemeOverField K) [Variety X] [Variety Y]
    (f : X ⟶ Y) [Flat f.left]
    (F : Y.left.Modules) [hcoh : F.IsCoherent] (k : ℤ)
    (hF : Y.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) (schemeTheoreticSupport F) ≤
      (k : EInt)) :
    CycleGroup.flatPullback (fun _ : Spec (CommRingCat.of K) ↦ 0) X Y f
        (SchemeOverField.relativeDimensionGap X Y f) k
        (relativeAssociatedCycle Y.hom (fun _ ↦ 0) F k) =
      relativeAssociatedCycle
        (hF := @pullback_isCoherent X.left Y.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom) f.left F hcoh)
        X.hom (fun _ ↦ 0) ((pullback f.left).obj F)
        (k + (SchemeOverField.relativeDimensionGap X Y f : ℤ)) := sorry

end AlgebraicGeometry.Scheme.Modules
