/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Local

/-!
# Target locality of regular immersions

This file records target locality of Koszul-regular, `H₁`-regular, and quasi-regular
immersions for morphisms of schemes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsKoszulRegularImmersion

/-- Koszul-regular immersions are local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f ↦ AlgebraicGeometry.IsKoszulRegularImmersion f) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsKoszulRegularImmersion

namespace AlgebraicGeometry.IsH1RegularImmersion

/-- `H₁`-regular immersions are local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f ↦ AlgebraicGeometry.IsH1RegularImmersion f) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsH1RegularImmersion

namespace AlgebraicGeometry.IsQuasiRegularImmersion

/-- Quasi-regular immersions are local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f ↦ AlgebraicGeometry.IsQuasiRegularImmersion f) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.IsQuasiRegularImmersion
