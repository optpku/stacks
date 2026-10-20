module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme

/-!
# Negative twists of invertible modules

The module `L(-D) = L ⊗ 𝒪(-D)` attached to an effective Cartier divisor, together
with the canonical inclusion `L(-D) ⟶ L` and the comparison between scheme-theoretic
vanishing on `D` and membership in global sections of `L(-D)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The negative twist `L(-D) = L ⊗ 𝒪(-D)` of a module by an effective Cartier divisor. -/
noncomputable abbrev negTwist (L : X.Modules) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] : X.Modules :=
  L ⊗ (D.negSheaf : X.Modules)

/-- The negative twist is the tensor product of `L` with the ideal sheaf of `D`. -/
theorem negTwist_eq (L : X.Modules) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    negTwist L D = L ⊗ (D.negSheaf : X.Modules) :=
  rfl

/-- The canonical inclusion `L(-D) ⟶ L` induced by the ideal sheaf `𝒪(-D) ⟶ 𝒪_X`. -/
noncomputable def negTwistIncl (L : X.Modules) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    negTwist L D ⟶ L :=
  (L ◁ (D.toSubobject.arrow ≫ (RingedSpace.unitIsoTensorUnit X.toRingedSpace).hom)) ≫
    (ρ_ L).hom

/-- Unfold the negative-twist inclusion as the unitor applied to the ideal inclusion. -/
theorem negTwistIncl_eq (L : X.Modules) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    negTwistIncl L D =
      (L ◁ (D.toSubobject.arrow ≫ (RingedSpace.unitIsoTensorUnit X.toRingedSpace).hom)) ≫
        (ρ_ L).hom :=
  rfl

/-- A global section of an invertible module vanishes on a closed subscheme when the
zero scheme of the section contains that subscheme. -/
def vanishesOnDivisor {L : X.Modules} [Invertible L] (s : L.sections)
    (D : X.IdealSheafData) : Prop :=
  @Scheme.zeroIdealSheaf X _ L (Invertible.tensorRight_isEquivalence ‹_›) s ≤ D

/-- A global section of `L` lies in `L(-D)` when it is the image of a global section of
the negative twist along the canonical inclusion. -/
def memNegTwist {L : X.Modules} (s : L.sections) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] : Prop :=
  ∃ t : (negTwist L D).sections, SheafOfModules.sectionsMap (negTwistIncl L D) t = s

/-- Vanishing on an effective Cartier divisor is equivalent to lying in the negative twist. -/
theorem vanishesOnDivisor_iff_memNegTwist {L : X.Modules} [Invertible L]
    (s : L.sections) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    vanishesOnDivisor s D ↔ memNegTwist s D :=
  sorry

end AlgebraicGeometry.Scheme.Modules
