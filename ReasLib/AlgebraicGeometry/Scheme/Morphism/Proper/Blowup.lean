module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IsomorphismLocus
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Blowup
import ReasLib.AlgebraicGeometry.Scheme.Blowup.Extension
import ReasLib.AlgebraicGeometry.Scheme.Blowup.Separation
import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.OpenImmersion

/-!
# Proper morphisms and admissible blowups

This module records when an admissible blowup makes the strict transform of a proper morphism
an isomorphism near the closure of a prescribed closed subset.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper morphism of quasi-compact quasi-separated schemes that is an isomorphism near a
closed subset of a quasi-compact open has, after an admissible blowup, a strict transform that
is an isomorphism near the closure of that subset. -/
theorem exists_isAdmissibleBlowup_strictTransform_isIso_near_closure
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f]
    (V : Y.Opens) [QuasiCompact V.ι]
    (T : TopologicalSpace.Closeds V)
    (hT : (T : Set V) ⊆ (f ∣_ V).isomorphismLocus) :
    ∃ (Y' : Scheme.{u}) (b : Y' ⟶ Y) (I : Y.IdealSheafData),
      IsAdmissibleBlowupCenter V b I ∧
        closure (b.base ⁻¹' Set.image V.ι.base (T : Set V)) ⊆
          (strictTransformSnd b (I.comap b) f).isomorphismLocus := sorry

end AlgebraicGeometry.Scheme.Hom
