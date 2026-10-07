module

public import ReasLib.AlgebraicGeometry.GroupoidScheme

/-!
# Conjugation descent data for a subgroupoid

This module constructs the isomorphism
`(r, (p, p')) ↦ ((p, p'), p⁻¹ ∘ r ∘ p')`
between the two pullbacks of a groupoid arrow scheme along `t × t` and `s × s`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The map `t_P × t_P` from pairs of `P`-arrows to pairs of objects of `G`. -/
def targetPair {S : Scheme.{u}} (G P : GroupoidScheme S) (hU : P.U = G.U) :
    P.R ⨯ P.R ⟶ G.U ⨯ G.U :=
  prod.map (P.t ≫ eqToHom hU) (P.t ≫ eqToHom hU)

/-- The first factor of `targetPair` is the transported target map. -/
theorem targetPair_fst {S : Scheme.{u}} (G P : GroupoidScheme S) (hU : P.U = G.U) :
    targetPair G P hU ≫ prod.fst = prod.fst ≫ P.t ≫ eqToHom hU := sorry

/-- The second factor of `targetPair` is the transported target map. -/
theorem targetPair_snd {S : Scheme.{u}} (G P : GroupoidScheme S) (hU : P.U = G.U) :
    targetPair G P hU ≫ prod.snd = prod.snd ≫ P.t ≫ eqToHom hU := sorry

/-- The map `s_P × s_P` from pairs of `P`-arrows to pairs of objects of `G`. -/
def sourcePair {S : Scheme.{u}} (G P : GroupoidScheme S) (hU : P.U = G.U) :
    P.R ⨯ P.R ⟶ G.U ⨯ G.U :=
  prod.map (P.s ≫ eqToHom hU) (P.s ≫ eqToHom hU)

/-- The first factor of `sourcePair` is the transported source map. -/
theorem sourcePair_fst {S : Scheme.{u}} (G P : GroupoidScheme S) (hU : P.U = G.U) :
    sourcePair G P hU ≫ prod.fst = prod.fst ≫ P.s ≫ eqToHom hU := sorry

/-- The second factor of `sourcePair` is the transported source map. -/
theorem sourcePair_snd {S : Scheme.{u}} (G P : GroupoidScheme S) (hU : P.U = G.U) :
    sourcePair G P hU ≫ prod.snd = prod.snd ≫ P.s ≫ eqToHom hU := sorry

/-- An arrow `r` of `G` and a pair `(p, p')` of `P`-arrows with the same targets
are composable as `r` after `p'`. -/
theorem conjugation_compose_source {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) (hU : P.U = G.U) :
    (pullback.fst G.toPreRelation.hom (targetPair G P hU) ≫ G.s) =
      (pullback.snd G.toPreRelation.hom (targetPair G P hU) ≫ prod.snd ≫ ι.arrow) ≫
        G.t := sorry

/-- After composing `r` with `p'`, the inverse of `p` is composable on the left. -/
theorem conjugation_compose_inverse {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) (hU : P.U = G.U) :
    ((pullback.snd G.toPreRelation.hom (targetPair G P hU) ≫ prod.fst ≫ ι.arrow) ≫
        G.i) ≫ G.s =
      (G.compose (pullback.fst G.toPreRelation.hom (targetPair G P hU))
          (pullback.snd G.toPreRelation.hom (targetPair G P hU) ≫ prod.snd ≫ ι.arrow)
          (conjugation_compose_source ι hU)) ≫ G.t := sorry

/-- The conjugated arrow `p⁻¹ ∘ r ∘ p'` of a point of the `t × t` pullback. -/
def conjugationArrow {S : Scheme.{u}} {G P : GroupoidScheme S} (ι : Hom P G)
    (hU : P.U = G.U) :
    pullback G.toPreRelation.hom (targetPair G P hU) ⟶ G.R :=
  G.compose
    ((pullback.snd G.toPreRelation.hom (targetPair G P hU) ≫ prod.fst ≫ ι.arrow) ≫ G.i)
    (G.compose (pullback.fst G.toPreRelation.hom (targetPair G P hU))
      (pullback.snd G.toPreRelation.hom (targetPair G P hU) ≫ prod.snd ≫ ι.arrow)
      (conjugation_compose_source ι hU))
    (conjugation_compose_inverse ι hU)

/-- The conjugated arrow is the groupoid composite `p⁻¹ ∘ r ∘ p'`. -/
theorem conjugationArrow_eq {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) (hU : P.U = G.U) :
    conjugationArrow ι hU =
      G.compose
        ((pullback.snd G.toPreRelation.hom (targetPair G P hU) ≫
            prod.fst ≫ ι.arrow) ≫ G.i)
        (G.compose (pullback.fst G.toPreRelation.hom (targetPair G P hU))
          (pullback.snd G.toPreRelation.hom (targetPair G P hU) ≫
            prod.snd ≫ ι.arrow)
          (conjugation_compose_source ι hU))
        (conjugation_compose_inverse ι hU) := sorry

/-- The pair `(p, p')` and the conjugated arrow lie over the same point of
`G.U ⨯ G.U` via `s × s` and `j`. -/
theorem conjugationHom_condition {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) (hU : P.U = G.U) :
    pullback.snd G.toPreRelation.hom (targetPair G P hU) ≫ sourcePair G P hU =
      conjugationArrow ι hU ≫ G.toPreRelation.hom := sorry

/-- The forward conjugation map
`(r, (p, p')) ↦ ((p, p'), p⁻¹ ∘ r ∘ p')`. -/
def conjugationHom {S : Scheme.{u}} {G P : GroupoidScheme S} (ι : Hom P G)
    (hU : P.U = G.U) :
    pullback G.toPreRelation.hom (targetPair G P hU) ⟶
      pullback (sourcePair G P hU) G.toPreRelation.hom :=
  pullback.lift (pullback.snd G.toPreRelation.hom (targetPair G P hU))
    (conjugationArrow ι hU) (conjugationHom_condition ι hU)

/-- An arrow `r'` of `G` and a pair `(p, p')` of `P`-arrows with the same sources
are composable as `r'` after `(p')⁻¹`. -/
theorem conjugation_inv_compose_source {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) (hU : P.U = G.U) :
    (pullback.snd (sourcePair G P hU) G.toPreRelation.hom ≫ G.s) =
      ((pullback.fst (sourcePair G P hU) G.toPreRelation.hom ≫
          prod.snd ≫ ι.arrow) ≫ G.i) ≫ G.t := sorry

/-- After composing `r'` with `(p')⁻¹`, the arrow `p` is composable on the left. -/
theorem conjugation_inv_compose_inverse {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) (hU : P.U = G.U) :
    (pullback.fst (sourcePair G P hU) G.toPreRelation.hom ≫ prod.fst ≫ ι.arrow) ≫
        G.s =
      (G.compose (pullback.snd (sourcePair G P hU) G.toPreRelation.hom)
          ((pullback.fst (sourcePair G P hU) G.toPreRelation.hom ≫
              prod.snd ≫ ι.arrow) ≫ G.i)
          (conjugation_inv_compose_source ι hU)) ≫ G.t := sorry

/-- The recovered arrow `p ∘ r' ∘ (p')⁻¹` of a point of the `s × s` pullback. -/
def conjugationInvArrow {S : Scheme.{u}} {G P : GroupoidScheme S} (ι : Hom P G)
    (hU : P.U = G.U) :
    pullback (sourcePair G P hU) G.toPreRelation.hom ⟶ G.R :=
  G.compose
    (pullback.fst (sourcePair G P hU) G.toPreRelation.hom ≫ prod.fst ≫ ι.arrow)
    (G.compose (pullback.snd (sourcePair G P hU) G.toPreRelation.hom)
      ((pullback.fst (sourcePair G P hU) G.toPreRelation.hom ≫
          prod.snd ≫ ι.arrow) ≫ G.i)
      (conjugation_inv_compose_source ι hU))
    (conjugation_inv_compose_inverse ι hU)

/-- The recovered arrow is the groupoid composite `p ∘ r' ∘ (p')⁻¹`. -/
theorem conjugationInvArrow_eq {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) (hU : P.U = G.U) :
    conjugationInvArrow ι hU =
      G.compose
        (pullback.fst (sourcePair G P hU) G.toPreRelation.hom ≫
          prod.fst ≫ ι.arrow)
        (G.compose (pullback.snd (sourcePair G P hU) G.toPreRelation.hom)
          ((pullback.fst (sourcePair G P hU) G.toPreRelation.hom ≫
              prod.snd ≫ ι.arrow) ≫ G.i)
          (conjugation_inv_compose_source ι hU))
        (conjugation_inv_compose_inverse ι hU) := sorry

/-- The recovered arrow and the pair `(p, p')` lie over the same point of
`G.U ⨯ G.U` via `j` and `t × t`. -/
theorem conjugationInv_condition {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) (hU : P.U = G.U) :
    conjugationInvArrow ι hU ≫ G.toPreRelation.hom =
      pullback.fst (sourcePair G P hU) G.toPreRelation.hom ≫
        targetPair G P hU := sorry

/-- The inverse conjugation map
`((p, p'), r') ↦ (p ∘ r' ∘ (p')⁻¹, (p, p'))`. -/
def conjugationInv {S : Scheme.{u}} {G P : GroupoidScheme S} (ι : Hom P G)
    (hU : P.U = G.U) :
    pullback (sourcePair G P hU) G.toPreRelation.hom ⟶
      pullback G.toPreRelation.hom (targetPair G P hU) :=
  pullback.lift (conjugationInvArrow ι hU)
    (pullback.fst (sourcePair G P hU) G.toPreRelation.hom)
    (conjugationInv_condition ι hU)

/-- Conjugation of arrows of `G` by pairs of `P`-arrows is an isomorphism over
`P.R ⨯ P.R`. -/
def conjugationIso {S : Scheme.{u}} {G P : GroupoidScheme S} (ι : Hom P G)
    (hU : P.U = G.U) :
    pullback G.toPreRelation.hom (targetPair G P hU) ≅
      pullback (sourcePair G P hU) G.toPreRelation.hom where
  hom := conjugationHom ι hU
  inv := conjugationInv ι hU
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward conjugation map is a morphism over `P.R ⨯ P.R`. -/
theorem conjugationIso_over {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) (hU : P.U = G.U) :
    (conjugationIso ι hU).hom ≫
        pullback.fst (sourcePair G P hU) G.toPreRelation.hom =
      pullback.snd G.toPreRelation.hom (targetPair G P hU) := sorry

/-- On `T`-valued points, the forward conjugation map sends `(r, (p, p'))` to
`p⁻¹ ∘ r ∘ p'`. -/
theorem conjugationIso_hom_spec {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) (hU : P.U = G.U) :
    (conjugationIso ι hU).hom ≫
        pullback.snd (sourcePair G P hU) G.toPreRelation.hom =
      conjugationArrow ι hU := sorry

/-- On `T`-valued points, the inverse conjugation map sends `((p, p'), r')` to
`p ∘ r' ∘ (p')⁻¹`. -/
theorem conjugationIso_inv_spec {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) (hU : P.U = G.U) :
    (conjugationIso ι hU).inv ≫
        pullback.fst G.toPreRelation.hom (targetPair G P hU) =
      conjugationInvArrow ι hU := sorry

/-- The conjugation isomorphism satisfies the cocycle identity
`φ₀₂ = φ₁₂ ∘ φ₀₁` on composable pairs of `P`-arrows. -/
theorem conjugationIso_cocycle {S : Scheme.{u}} {G P : GroupoidScheme S}
    (ι : Hom P G) {T : Over S} (r : T ⟶ G.R) (p₁ p₁' p₂ p₂' : T ⟶ P.R)
    (h_p : (p₁ ≫ ι.arrow) ≫ G.s = (p₂ ≫ ι.arrow) ≫ G.t)
    (h_p' : (p₁' ≫ ι.arrow) ≫ G.s = (p₂' ≫ ι.arrow) ≫ G.t)
    (h_r : r ≫ G.s = (p₁' ≫ ι.arrow) ≫ G.t)
    (h_r' : r ≫ G.s = G.compose (p₁' ≫ ι.arrow) (p₂' ≫ ι.arrow) h_p' ≫ G.t)
    (h_inv₁ : ((p₁ ≫ ι.arrow) ≫ G.i) ≫ G.s =
      G.compose r (p₁' ≫ ι.arrow) h_r ≫ G.t)
    (h_mid : G.compose ((p₁ ≫ ι.arrow) ≫ G.i)
          (G.compose r (p₁' ≫ ι.arrow) h_r) h_inv₁ ≫ G.s =
        (p₂' ≫ ι.arrow) ≫ G.t)
    (h_inv₂ : ((p₂ ≫ ι.arrow) ≫ G.i) ≫ G.s =
      G.compose
          (G.compose ((p₁ ≫ ι.arrow) ≫ G.i)
            (G.compose r (p₁' ≫ ι.arrow) h_r) h_inv₁)
          (p₂' ≫ ι.arrow) h_mid ≫ G.t)
    (h_comp : (G.compose (p₁ ≫ ι.arrow) (p₂ ≫ ι.arrow) h_p ≫ G.i) ≫ G.s =
      G.compose r (G.compose (p₁' ≫ ι.arrow) (p₂' ≫ ι.arrow) h_p') h_r' ≫
        G.t) :
    G.compose (G.compose (p₁ ≫ ι.arrow) (p₂ ≫ ι.arrow) h_p ≫ G.i)
        (G.compose r (G.compose (p₁' ≫ ι.arrow) (p₂' ≫ ι.arrow) h_p') h_r')
        h_comp =
      G.compose ((p₂ ≫ ι.arrow) ≫ G.i)
        (G.compose
          (G.compose ((p₁ ≫ ι.arrow) ≫ G.i)
            (G.compose r (p₁' ≫ ι.arrow) h_r) h_inv₁)
          (p₂' ≫ ι.arrow) h_mid)
        h_inv₂ := sorry

end AlgebraicGeometry.GroupoidScheme

