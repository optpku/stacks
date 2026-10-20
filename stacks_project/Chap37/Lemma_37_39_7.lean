module

public import ReasLib.AlgebraicGeometry.Scheme.ArtinApproximation.TwoStage.Etale
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits IsLocalRing

universe u

namespace AlgebraicGeometry.ArtinApproximation

/- Lemma 37.39.7: if the local comparison map induces a bijection on maximal-ideal
completions, then the two-stage approximation diagram can be chosen with an étale comparison
morphism. -/
@[stacks 0CB1]
#check (AlgebraicGeometry.ArtinApproximation.exists_twoStageApproximation_etale.{u} :
  ∀ {S T X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ T) (q : T ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType pX]
    [LocallyOfFiniteType pY] [LocallyOfFiniteType q]
    (s : S) (t : T) (x : X) (y : Y)
    (hx : pX x = s) (hy : pY y = t) (ht : q t = s)
    [IsGRing (S.presheaf.stalk s)]
    (σ : T.presheaf.stalk t →+*
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))
    [IsLocalHom σ]
    (hσ_over :
      σ.comp (ht ▸ (q.stalkMap t).hom) =
        (algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
            (S.presheaf.stalk s)))),
    let j : Spec (CommRingCat.of
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s))) ⟶ T :=
      Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t;
    let Yσ : Scheme.{u} := pullback pY j;
    ∀ (yσ : Yσ)
        (hyσY : pullback.fst pY j yσ = y)
        (hyσShat : pullback.snd pY j yσ =
          closedPoint (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
            (S.presheaf.stalk s)))
        (hyσ_unique : ∀ z : Yσ,
          pullback.fst pY j z = y →
            pullback.snd pY j z =
              closedPoint (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                (S.presheaf.stalk s)) → z = yσ)
        (φ : X.presheaf.stalk x →+*
          AdicCompletion (maximalIdeal (Yσ.presheaf.stalk yσ)) (Yσ.presheaf.stalk yσ))
        [IsLocalHom φ]
        (hφ_over : φ.comp (hx ▸ (pX.stalkMap x).hom) =
          (algebraMap (Yσ.presheaf.stalk yσ)
            (AdicCompletion (maximalIdeal (Yσ.presheaf.stalk yσ))
              (Yσ.presheaf.stalk yσ))).comp
            ((hyσY ▸ (pullback.fst pY j).stalkMap yσ).hom.comp
              ((hy ▸ (pY.stalkMap y).hom).comp (ht ▸ (q.stalkMap t).hom))))
        (hφ_completion : Function.Bijective (AdicCompletion.mapLocal φ)),
        ∀ (N : ℕ), 1 ≤ N →
          ∃ (V : Scheme.EtaleNeighborhood S s) (hV : V.IsElementary),
            let VEtale := V.toEtale
            let VScheme := VEtale.left
            ∃ (τ : VScheme ⟶ T)
              (hτS : τ ≫ q = VEtale.hom) (hτt : τ V.point = t)
              (hσN : ∀ a : T.presheaf.stalk t,
                (V.map_point ▸ AdicCompletion.mapLocal
                    (VEtale.hom.stalkMap V.point).hom) (σ a) -
                    algebraMap (VScheme.presheaf.stalk V.point)
                      (AdicCompletion
                        (maximalIdeal (VScheme.presheaf.stalk V.point))
                        (VScheme.presheaf.stalk V.point))
                      ((hτt ▸ (τ.stalkMap V.point).hom) a) ∈
          AdicCompletion.extendedIdealPow
                    (maximalIdeal (VScheme.presheaf.stalk V.point)) N),
            let XV : Scheme.{u} := pullback pX V.toEtale.hom
            let YV : Scheme.{u} := pullback pY τ
            ∃ (xv : XV) (hxvX : pullback.fst pX V.toEtale.hom xv = x)
                (hxvV : pullback.snd pX V.toEtale.hom xv = V.point)
                (yv : YV) (hyvY : pullback.fst pY τ yv = y)
                (hyvV : pullback.snd pY τ yv = V.point)
                (W : Scheme.EtaleNeighborhood YV yv) (hW : W.IsElementary),
                let WEtale := W.toEtale
                let WScheme := WEtale.left
                ∃ (f : WScheme ⟶ XV)
                (hfV : f ≫ pullback.snd pX V.toEtale.hom =
                  WEtale.hom ≫ pullback.snd pY τ)
                (hfw : f W.point = xv)
                (hf_etale : Etale f),
              ∃ (e :
                    (Yσ.presheaf.stalk yσ ⧸ maximalIdeal (Yσ.presheaf.stalk yσ) ^ N) ≃+*
                      (YV.presheaf.stalk yv ⧸ maximalIdeal (YV.presheaf.stalk yv) ^ N))
                  (heY : ∀ a : Y.presheaf.stalk y,
                    e (Ideal.Quotient.mk (maximalIdeal (Yσ.presheaf.stalk yσ) ^ N)
                        ((hyσY ▸ (pullback.fst pY j).stalkMap yσ).hom a)) =
                      Ideal.Quotient.mk (maximalIdeal (YV.presheaf.stalk yv) ^ N)
                        ((hyvY ▸ (pullback.fst pY τ).stalkMap yv).hom a))
                  (heBase : ∀ b : AdicCompletion
                      (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s),
                    e (Ideal.Quotient.mk (maximalIdeal (Yσ.presheaf.stalk yσ) ^ N)
                        ((hyσShat ▸ (pullback.snd pY j).stalkMap yσ).hom
                          ((stalkClosedPointIso (CommRingCat.of
                            (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
                              (S.presheaf.stalk s)))).inv.hom b))) =
                      (hyvV ▸ Ideal.quotientMap
                        (maximalIdeal (YV.presheaf.stalk yv) ^ N)
                        ((pullback.snd pY τ).stalkMap yv).hom
                        (RingHom.IsLocalHom.pow_maximalIdeal_le_comap
                          ((pullback.snd pY τ).stalkMap yv).hom N))
                        (AdicCompletion.evalₐ
                          (maximalIdeal (VScheme.presheaf.stalk V.point)) N
                          ((V.map_point ▸ AdicCompletion.mapLocal
                            (VEtale.hom.stalkMap V.point).hom) b))),
                ∀ a : X.presheaf.stalk x,
                    (W.map_point ▸ Ideal.quotientMap
                      (maximalIdeal (WScheme.presheaf.stalk W.point) ^ N)
                      (WEtale.hom.stalkMap W.point).hom
                      (RingHom.IsLocalHom.pow_maximalIdeal_le_comap
                        (WEtale.hom.stalkMap W.point).hom N))
                      (e (AdicCompletion.evalₐ
                          (maximalIdeal (Yσ.presheaf.stalk yσ)) N (φ a))) =
                      Ideal.Quotient.mk
                        (maximalIdeal (WScheme.presheaf.stalk W.point) ^ N)
                        ((hfw ▸ (f.stalkMap W.point).hom)
                          ((hxvX ▸ (pullback.fst pX V.toEtale.hom).stalkMap xv).hom a)))

end AlgebraicGeometry.ArtinApproximation
