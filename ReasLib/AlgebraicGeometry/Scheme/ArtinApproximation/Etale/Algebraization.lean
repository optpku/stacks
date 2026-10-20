/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import ReasLib.AlgebraicGeometry.Scheme.ArtinApproximation.Etale.CommonNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Point

@[expose] public section

open CategoryTheory Limits IsLocalRing

universe u

namespace AlgebraicGeometry.ArtinApproximation

/-- A compatible isomorphism of completed local rings over the completion of a G-ring stalk
yields elementary étale neighborhoods of the source points and an elementary étale comparison
with the corresponding base change. -/
theorem exists_elementaryEtaleDiagram
    {S T X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ T)
    [IsLocallyNoetherian S] [Scheme.Hom.FiniteType (specULiftZIsTerminal.from T)]
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (s : S) (t : T) (x : X) (y : Y) (hx : pX x = s) (hy : pY y = t)
    [IsGRing (S.presheaf.stalk s)]
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    [IsLocalHom σ] :
    let Rhat := AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)
    let j : Spec (CommRingCat.of Rhat) ⟶ T :=
      Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t
    let Yσ : Scheme.{u} := pullback pY j
    let qσ : Yσ ⟶ Spec (CommRingCat.of Rhat) := pullback.snd pY j
    ∀ (yσ : Yσ) (hyσY : pullback.fst pY j yσ = y)
        (hyσRhat : qσ yσ = closedPoint Rhat)
        (φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
          AdicCompletion (maximalIdeal (Yσ.presheaf.stalk yσ)) (Yσ.presheaf.stalk yσ))
        (hφ_over :
          φ.toRingHom.comp (hx ▸ AdicCompletion.mapLocal (pX.stalkMap x).hom) =
            (algebraMap (Yσ.presheaf.stalk yσ)
              (AdicCompletion (maximalIdeal (Yσ.presheaf.stalk yσ))
                (Yσ.presheaf.stalk yσ))).comp
              ((hyσRhat ▸ (qσ.stalkMap yσ).hom).comp
                (stalkClosedPointIso (CommRingCat.of Rhat)).inv.hom)),
      ∃ (V : Scheme.EtaleNeighborhood.Elementary S s),
        let VEtale := V.obj.toEtale
        ∃ (τ : VEtale.left ⟶ T) (hτt : τ V.obj.point = t),
        let Yτ : Scheme.{u} := pullback pY τ
        let qτ : Yτ ⟶ VEtale.left := pullback.snd pY τ
        ∃ (e : qσ.fiber (closedPoint Rhat) ≅ qτ.fiber V.obj.point)
            (heY : e.hom ≫ qτ.fiberι V.obj.point ≫ pullback.fst pY τ =
              qσ.fiberι (closedPoint Rhat) ≫ pullback.fst pY j),
          let yτ : Yτ := qτ.fiberι V.obj.point
            (e.hom (hyσRhat ▸ qσ.asFiber yσ))
          ∃ (hyτY : pullback.fst pY τ yτ = y)
              (hyτV : pullback.snd pY τ yτ = V.obj.point)
              (W : Scheme.EtaleNeighborhood.Elementary X x),
            let WEtale := W.obj.toEtale
            ∃ (h : WEtale.left ⟶ Yτ)
              (h_etale : Etale h) (h_point : h W.obj.point = yτ)
              (h_residue : IsIso (h.residueFieldMap W.obj.point)),
            WEtale.hom ≫ pX = h ≫ pullback.snd pY τ ≫ VEtale.hom := sorry

end AlgebraicGeometry.ArtinApproximation
