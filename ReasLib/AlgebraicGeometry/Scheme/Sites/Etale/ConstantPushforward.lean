/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- On an integral normal scheme, the small-étale direct image of the constant
sheaf on `E` along the inclusion of the function-field generic point is
isomorphic to the constant sheaf on `E`. -/
theorem pushforward_constantSheaf_genericPoint {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal) (E : Type u)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasWeakSheafify (Spec X.functionField).smallEtaleTopology (Type u)] :
    Nonempty
      ((smallEtaleDirectImage (X.fromSpecStalk (genericPoint X))).obj
          ((constantSheaf (Spec X.functionField).smallEtaleTopology (Type u)).obj E) ≅
        (constantSheaf X.smallEtaleTopology (Type u)).obj E) := sorry

/-- On an integral normal scheme, the small-étale direct image of the constant
sheaf on `E` along the inclusion of a nonempty open subscheme is isomorphic to
the constant sheaf on `E`. -/
theorem pushforward_constantSheaf_opensι {X : Scheme.{u}} [IsIntegral X]
    (hX : X.isNormal) (U : X.Opens) [Nonempty U] (E : Type u)
    [HasWeakSheafify X.smallEtaleTopology (Type u)]
    [HasWeakSheafify U.toScheme.smallEtaleTopology (Type u)] :
    Nonempty
      ((smallEtaleDirectImage U.ι).obj
          ((constantSheaf U.toScheme.smallEtaleTopology (Type u)).obj E) ≅
        (constantSheaf X.smallEtaleTopology (Type u)).obj E) := sorry

end AlgebraicGeometry.Scheme
