/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicTypes

/-!
# Adic* and locally adic* formal algebraic spaces

Natural-number-indexed thickening colimits, quotient-power presentations, and
adic* conditions for sheaves on a chosen big fppf site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry TopologicalRing

universe u v

#check
  (AlgebraicGeometry.IsNatDirectedAffineThickeningColimit :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      (D : ℕ ⥤ 𝒮.bigAffineSite S)
      (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

#check
  (AlgebraicGeometry.IsAdicPowerPresentation :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      {A : Type u} [CommRing A] [TopologicalSpace A] [IsAdicRing A]
      (I : Ideal A) (D : ℕ ⥤ 𝒮.bigAffineSite S)
      (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (e : ∀ n, ((𝒮.bigAffineToScheme S).obj (D.obj n)) ≅
        Spec (CommRingCat.of (A ⧸ I ^ (n + 1)))), Prop)

#check
  (AlgebraicGeometry.IsAdicStar :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
      (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

#check
  (AlgebraicGeometry.IsLocallyAdicStar :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
      [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
      [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
      (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)
