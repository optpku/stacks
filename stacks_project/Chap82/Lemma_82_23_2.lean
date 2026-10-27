/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 82.23.2: The refined Gysin homomorphism sends rational boundaries
to rational boundaries and hence induces a homomorphism on Chow groups.
On cycle representatives it is the Chow class of refined intersection. -/
@[stacks 0ERA] #check (AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin.gysin :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (L : X.Modules) [isInvertibleObject L] (s : L.sections) (k : ℤ),
      Hom.chowGroup pX δ (k + 1) →+
        Hom.chowGroup (zeroSchemeι L s ≫ pX) δ k)
