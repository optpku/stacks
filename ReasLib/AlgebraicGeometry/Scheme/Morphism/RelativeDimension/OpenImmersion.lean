/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.QuasiFinite

/-!
# Relative dimension of open immersions

Open immersions have relative dimension zero.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An open immersion has relative dimension zero. -/
theorem relativeDimension_zero_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : RelativeDimension f 0 := sorry

/-- An open immersion of an open subscheme has relative dimension zero. -/
instance instRelativeDimensionZero_opensι {X : Scheme.{u}} (U : X.Opens) :
    RelativeDimension U.ι 0 :=
  relativeDimension_zero_of_isOpenImmersion _

/-- The open immersion of a nested open has relative dimension zero. -/
instance instRelativeDimensionZero_homOfLE {X : Scheme.{u}} {U V : X.Opens}
    (hUV : U ≤ V) : RelativeDimension (X.homOfLE hUV) 0 :=
  relativeDimension_zero_of_isOpenImmersion _

/-- The identity morphism has relative dimension zero. -/
instance instRelativeDimensionZero_id {X : Scheme.{u}} :
    RelativeDimension (𝟙 X) 0 :=
  relativeDimension_zero_of_isOpenImmersion _

end AlgebraicGeometry.Scheme.Hom
