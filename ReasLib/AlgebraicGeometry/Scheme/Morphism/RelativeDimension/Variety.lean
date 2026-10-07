module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Relative dimension of flat morphisms of varieties

This file gives the canonical relative-dimension gap of a morphism between varieties and
records that a flat morphism has this relative dimension.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {K : Type u} [Field K]

/-- The canonical natural-valued dimension gap attached to a morphism between varieties. -/
noncomputable def relativeDimensionGap
    (X Y : SchemeOverField K) [Variety X] [Variety Y] (f : X ⟶ Y) : ℕ :=
  Int.toNat
    (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)
        (genericPoint X.left) -
      Y.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)
        (genericPoint Y.left))

/-- For a flat morphism of varieties, the integer coercion of its canonical relative-dimension
gap is the difference of the dimensions measured at the generic points. -/
theorem relativeDimensionGap_spec
    (X Y : SchemeOverField K) [Variety X] [Variety Y]
    (f : X ⟶ Y) [Flat f.left] :
    (relativeDimensionGap X Y f : ℤ) =
      X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)
          (genericPoint X.left) -
        Y.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0)
          (genericPoint Y.left) := sorry

/-- A flat morphism between varieties has the canonical dimension gap as its fixed relative
dimension. -/
theorem relativeDimension_gap_of_flat
    (X Y : SchemeOverField K) [Variety X] [Variety Y]
    (f : X ⟶ Y) [Flat f.left] :
    Scheme.Hom.RelativeDimension f.left (relativeDimensionGap X Y f) := sorry

/-- Fixed relative dimension for a flat morphism between varieties, indexed by its canonical
dimension gap. -/
instance instRelativeDimensionGapOfFlat
    (X Y : SchemeOverField K) [Variety X] [Variety Y]
    (f : X ⟶ Y) [Flat f.left] :
    Scheme.Hom.RelativeDimension f.left (relativeDimensionGap X Y f) :=
  relativeDimension_gap_of_flat X Y f

end AlgebraicGeometry.SchemeOverField
