/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct

/-!
# Normalization through generic-point residue fields

This leaf gives the absolute normalization notation used throughout scheme
arguments and records the coverage of the generic points of a relative
normalization by generic points of its source.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u})
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

/-- The underlying scheme `X^ν`, obtained by normalizing the generic-point coproduct map. -/
noncomputable abbrev normalization : Scheme.{u} :=
  (genericPointSpectrumCoproductTo X).normalization

/-- The canonical normalization morphism `X.normalization ⟶ X`. -/
noncomputable abbrev normalizationTo :
    X.normalization ⟶ X :=
  (genericPointSpectrumCoproductTo X).fromNormalization

/-- The absolute normalization is the relative normalization of the generic-point coproduct map. -/
@[simp]
theorem normalization_eq :
    X.normalization = (genericPointSpectrumCoproductTo X).normalization := rfl

/-- The absolute normalization morphism is the relative normalization morphism of the generic-point
coproduct map. -/
@[simp]
theorem normalizationTo_eq :
    X.normalizationTo = (genericPointSpectrumCoproductTo X).fromNormalization := rfl

end Scheme

namespace Scheme.Hom

/-- Every generic point of the relative normalization of a quasi-compact and
quasi-separated morphism is the image of a generic point of its source. -/
theorem surjOn_genericPoints_toNormalization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] :
    Set.SurjOn f.toNormalization (genericPoints Y) (genericPoints f.normalization) := sorry

end Scheme.Hom

end AlgebraicGeometry
