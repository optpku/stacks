module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.ClosedImmersion.Comparison

/-!
# Morphism properties of closed-immersion pushout comparisons

The morphism induced between pushouts of closed immersions has the standard local
morphism properties exactly when both component morphisms do.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Pushout.ClosedImmersion

variable {Z X Y : Scheme.{u}}

/-- The induced morphism of pushouts is locally of finite type exactly when both
component morphisms are locally of finite type. -/
theorem inducedMap_locallyOfFiniteType_iff (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    LocallyOfFiniteType (inducedMap i j P) ↔
      LocallyOfFiniteType P.fst.hom ∧ LocallyOfFiniteType P.snd.hom := sorry

/-- The induced morphism of pushouts is flat exactly when both component
morphisms are flat. -/
theorem inducedMap_flat_iff (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    Flat (inducedMap i j P) ↔ Flat P.fst.hom ∧ Flat P.snd.hom := sorry

/-- The induced morphism of pushouts is flat and locally of finite presentation
exactly when both component morphisms have both properties. -/
theorem inducedMap_flat_locallyOfFinitePresentation_iff (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    (Flat (inducedMap i j P) ∧ LocallyOfFinitePresentation (inducedMap i j P)) ↔
      (Flat P.fst.hom ∧ LocallyOfFinitePresentation P.fst.hom) ∧
        (Flat P.snd.hom ∧ LocallyOfFinitePresentation P.snd.hom) := sorry

/-- The induced morphism of pushouts is smooth exactly when both component
morphisms are smooth. -/
theorem inducedMap_smooth_iff (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    Smooth (inducedMap i j P) ↔ Smooth P.fst.hom ∧ Smooth P.snd.hom := sorry

/-- The induced morphism of pushouts is étale exactly when both component
morphisms are étale. -/
theorem inducedMap_etale_iff (i : Z ⟶ X) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (P : CategoricalPullback (Over.pullback i) (Over.pullback j)) :
    Etale (inducedMap i j P) ↔ Etale P.fst.hom ∧ Etale P.snd.hom := sorry

end AlgebraicGeometry.Scheme.Pushout.ClosedImmersion
