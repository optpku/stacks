/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Pushforward

/-!
# Maps of pushforward structure algebras

Precomposition induces a morphism between the pushforward structure algebras of
quasi-compact quasi-separated morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The `𝒪_Y`-algebra map `f_* 𝒪_X ⟶ (g ≫ f)_* 𝒪_Z` induced by precomposition
with `g`. -/
def pushforwardStructureQcAlgebraMap {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (g : Z ⟶ X) [QuasiCompact (g ≫ f)]
    [QuasiSeparated (g ≫ f)] :
    (pushforwardStructureQcAlgebra f).obj ⟶
      (pushforwardStructureQcAlgebra (g ≫ f)).obj :=
  Under.homMk
    ((commRingPushforward f).map (commStructureSheafMap g) ≫
      (commRingPushforwardComp g f).hom.app (commStructureSheaf Z))
    sorry

/-- The underlying sheaf morphism of `pushforwardStructureQcAlgebraMap` is
pushforward of `g^♯` followed by the associator. -/
theorem pushforwardStructureQcAlgebraMap_right {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Z ⟶ X)
    [QuasiCompact (g ≫ f)] [QuasiSeparated (g ≫ f)] :
    (pushforwardStructureQcAlgebraMap f g).right =
      (commRingPushforward f).map (commStructureSheafMap g) ≫
        (commRingPushforwardComp g f).hom.app (commStructureSheaf Z) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
