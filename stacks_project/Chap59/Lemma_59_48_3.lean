module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 59.48.3 (1): If `f : X ⟶ Y` is a closed immersion and `p : U ⟶ X` is
syntomic, then syntomic morphisms `V i ⟶ Y` have pullbacks over `X` mapping to
`U` as a Zariski covering. -/
@[stacks 04E3] #check
  (AlgebraicGeometry.exists_zariskiCover_of_closedImmersion_syntomic :
    ∀ {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
      (p : U ⟶ X) [Syntomic p],
      ∃ (I : Type u) (V : I → Scheme.{u}) (g : ∀ i, V i ⟶ Y),
        (∀ i, Syntomic (g i)) ∧
          ∃ (h : ∀ i, (pullback (g i) f : Scheme.{u}) ⟶ U),
            (∀ i, pullback.snd (g i) f = h i ≫ p) ∧
              Presieve.ofArrows (fun i ↦ (pullback (g i) f : Scheme.{u})) h ∈
                Scheme.zariskiPrecoverage U)

/- Lemma 59.48.3 (2): If `f : X ⟶ Y` is a closed immersion and `p : U ⟶ X` is
smooth, then smooth morphisms `V i ⟶ Y` have pullbacks over `X` mapping to
`U` as a Zariski covering. -/
@[stacks 04E3] #check
  (AlgebraicGeometry.exists_zariskiCover_of_closedImmersion_smooth :
    ∀ {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
      (p : U ⟶ X) [Smooth p],
      ∃ (I : Type u) (V : I → Scheme.{u}) (g : ∀ i, V i ⟶ Y),
        (∀ i, Smooth (g i)) ∧
          ∃ (h : ∀ i, (pullback (g i) f : Scheme.{u}) ⟶ U),
            (∀ i, pullback.snd (g i) f = h i ≫ p) ∧
              Presieve.ofArrows (fun i ↦ (pullback (g i) f : Scheme.{u})) h ∈
                Scheme.zariskiPrecoverage U)

/- Lemma 59.48.3 (3): If `f : X ⟶ Y` is a closed immersion and `p : U ⟶ X` is
étale, then étale morphisms `V i ⟶ Y` have pullbacks over `X` mapping to
`U` as a Zariski covering. -/
@[stacks 04E3] #check
  (AlgebraicGeometry.exists_zariskiCover_of_closedImmersion_etale :
    ∀ {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
      (p : U ⟶ X) [Etale p],
      ∃ (I : Type u) (V : I → Scheme.{u}) (g : ∀ i, V i ⟶ Y),
        (∀ i, Etale (g i)) ∧
          ∃ (h : ∀ i, (pullback (g i) f : Scheme.{u}) ⟶ U),
            (∀ i, pullback.snd (g i) f = h i ≫ p) ∧
              Presieve.ofArrows (fun i ↦ (pullback (g i) f : Scheme.{u})) h ∈
                Scheme.zariskiPrecoverage U)
