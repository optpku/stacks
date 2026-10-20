/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig.FppfPushforward

/-!
# Small-étale to big-fppf inverse-image comparison

The inverse-image square underlying the proper small-étale to big-fppf
pushforward comparison.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

#check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.fppfSmallInverseImageSquare :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology (Type (u + 1))]
      [HasSheafify Y.smallEtaleTopology (Type (u + 1))],
      (AlgebraicGeometry.Scheme.Etale.SmallToBig.fppfComparison Y)⁻¹ ⋙
          (AlgebraicGeometry.Scheme.Fppf.Big.morphismOfTopoi f)⁻¹ ≅
        (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallMorphism f)⁻¹ ⋙
          (AlgebraicGeometry.Scheme.Etale.SmallToBig.fppfComparison X)⁻¹)

end AlgebraicGeometry.Scheme.Etale.SmallToBig

end

end
