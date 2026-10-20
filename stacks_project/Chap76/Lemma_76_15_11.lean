/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.EtaleLocal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

/- Lemma 76.15.11 (1): Let `S` be a scheme. Let `h : Z ⟶ X` be a formally
unramified morphism of algebraic spaces over `S`, and let `V ⟶ U` over
`Z ⟶ X` be a commutative square with étale vertical arrows. Then `V ⟶ U` is
formally unramified. -/
@[stacks 060D]
#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.of_etaleCommSq :
    ∀ {S : Scheme.{u}} {X Z U V : AlgebraicSpace S}
      (fVU : V ⟶ U) (fVZ : V ⟶ Z) (fUX : U ⟶ X) (h : Z ⟶ X)
      [FormallyUnramified h] [Etale fVZ] [Etale fUX]
      (sq : CommSq fVU fVZ fUX h), FormallyUnramified fVU)

/- Lemma 76.15.11 (2): If `Z'` is a universal first-order thickening of `Z`
over `X` and `V'` is a universal first-order thickening of `V` over `U`, then
the canonical comparison `V' ⟶ Z'` is étale. -/
@[stacks 060D]
#check (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.comparison_etale :
    ∀ {S : Scheme.{u}} {X Z U V Z' V' : AlgebraicSpace S}
      (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iV : V ⟶ V') (fV : V' ⟶ U)
      (fVZ : V ⟶ Z) (fUX : U ⟶ X)
      [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iV fV]
      [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iV ≫ fV)]
      [Etale fVZ] [Etale fUX]
      (sq : CommSq fVZ (iV ≫ fV) (iZ ≫ fZ) fUX),
      Etale (IsUniversalFirstOrder.comparison iV fV iZ fZ fVZ fUX sq))

/- Lemma 76.15.11 (3): In particular the canonical map
`(Modules.pullback fVZ).obj (Hom.conormalSheaf iZ) ⟶ Hom.conormalSheaf iV` is an
isomorphism, so `C_{Z/X}` restricted along `V ⟶ Z` is identified with
`C_{V/U}`. -/
@[stacks 060D]
#check (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.conormalMap_isIso_of_etale :
    ∀ {S : Scheme.{u}} {X Z U V Z' V' : AlgebraicSpace S}
      (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iV : V ⟶ V') (fV : V' ⟶ U)
      (fVZ : V ⟶ Z) (fUX : U ⟶ X)
      [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iV fV]
      [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iV ≫ fV)]
      [Etale fVZ] [Etale fUX]
      (sq : CommSq fVZ (iV ≫ fV) (iZ ≫ fZ) fUX),
      IsIso (IsUniversalFirstOrder.conormalMap iV fV iZ fZ fVZ fUX sq))
