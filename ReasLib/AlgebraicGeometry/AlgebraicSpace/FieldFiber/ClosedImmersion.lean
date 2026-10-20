/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage

/-!
# Closed immersions of field-valued fibres

The inclusion of a fibre over a closed field-valued point is a closed immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The scheme-theoretic fibre inclusion of a closed field-valued point is a closed
immersion. -/
instance instIsClosedImmersion_fieldFiberι {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (p : FieldValuedPoint Y) [IsClosedImmersion p.hom] :
    IsClosedImmersion (fieldFiberι f p) :=
  IsClosedImmersion.of_isPullback (fieldFiber_isPullback f p)

end AlgebraicGeometry.AlgebraicSpace
