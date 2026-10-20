/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage

/-!
# Function fields of scheme-theoretic images

This leaf specializes the generic-point function-field API to Mathlib's
canonical factorization through `Scheme.Hom.image`.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The scheme-theoretic image of a morphism from an integral scheme is integral. -/
theorem isIntegral_image_of_isIntegral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] :
    IsIntegral f.image := sorry

/-- Integrality of a scheme-theoretic image is inferred from integrality of the source. -/
instance instIsIntegralImageOfIsIntegral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] :
    IsIntegral f.image :=
  isIntegral_image_of_isIntegral f

/-- The canonical map to the scheme-theoretic image sends the generic point to the generic point. -/
theorem toImage_map_genericPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] :
    f.toImage (genericPoint X) = genericPoint f.image := sorry

/-- The function-field map induced by the canonical dominant morphism to a scheme-theoretic
image. -/
noncomputable def toImageFunctionFieldMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] :
    f.image.functionField →+* X.functionField :=
  f.toImage.functionFieldMap (f.toImage_map_genericPoint)

/-- The function-field map of `f.toImage` is the generic-point function-field map specialized
to `toImage_map_genericPoint`. -/
theorem toImageFunctionFieldMap_def
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] :
    f.toImageFunctionFieldMap =
      f.toImage.functionFieldMap (f.toImage_map_genericPoint) := sorry

/-- The canonical algebra structure on the function field of the source over the function field
of its scheme-theoretic image. -/
@[reducible]
noncomputable def toImageFunctionFieldAlgebra
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] :
    Algebra f.image.functionField X.functionField :=
  (f.toImageFunctionFieldMap).toAlgebra

/-- The function-field extension induced by `f.toImage` is available to typeclass search. -/
noncomputable instance instAlgebraToImageFunctionField
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] :
    Algebra f.image.functionField X.functionField :=
  f.toImageFunctionFieldAlgebra

/-- The algebra map for the `toImage` function-field extension is
`toImageFunctionFieldMap`. -/
theorem algebraMap_toImageFunctionFieldAlgebra
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] :
    letI : Algebra f.image.functionField X.functionField := f.toImageFunctionFieldAlgebra
    algebraMap f.image.functionField X.functionField = f.toImageFunctionFieldMap := sorry

end AlgebraicGeometry.Scheme.Hom
