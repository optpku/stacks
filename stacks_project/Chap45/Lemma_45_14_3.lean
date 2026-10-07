module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.Blowup

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open scoped DirectSum

noncomputable section

universe u

/- Lemma 45.14.3: for a positive pure-codimension smooth center whose conormal `K₀` class
extends from the ambient smooth projective scheme, a specified refined Gysin class admits a
common exceptional Chow class satisfying the exceptional-divisor product and pushforward
relations. -/
@[stacks 0FIH] #check
  (AlgebraicGeometry.IsBlowup.existsBlowupExceptionalCycle :
    ∀ {k : Type u} [Field k] {X X' : SchemeOverField k}
      [Smooth X.hom] [Projective X.hom]
      (I : X.left.IdealSheafData) [Smooth (I.subschemeι ≫ X.hom)]
      (b : X' ⟶ X) [IsBlowup b.left I] (r : ℕ), 0 < r →
      TopologicalSpace.HasPureCodimension (I.support : Set X.left) r →
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r
        (Scheme.Hom.conormalSheaf I.subschemeι)] →
      (∃ α : Scheme.K0 X.left,
        Scheme.K0.pullback I.subschemeι α =
          Scheme.VectorBundleK0.toK0 I.subscheme
            (ObjectProperty.GrothendieckGroup.of
              (SheafOfModules.IsFiniteLocallyFree : ObjectProperty I.subscheme.Modules)
              ⟨Scheme.Hom.conormalSheaf I.subschemeι,
                Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
                  r (Scheme.Hom.conormalSheaf I.subschemeι)⟩)) →
      ∀ centerGysin : BivariantClass (fun _ ↦ 0)
          (overHom (I.subschemeι ≫ X.hom) X.hom I.subschemeι rfl) (r : ℤ),
        (∀ n : ℤ,
          centerGysin.cap (𝟙 _)
              (overHom (I.subschemeι ≫ X.hom) X.hom I.subschemeι rfl)
              (𝟙 _) IsPullback.of_id_fst n
              (@chowClass X.left
                (LocallyOfFiniteType.isLocallyNoetherian X.hom)
                (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n
                (@CycleGroup.fundamental X.left
                  (LocallyOfFiniteType.isLocallyNoetherian X.hom)
                  (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)) =
            @chowClass I.subscheme
              (LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ X.hom))
              ((I.subschemeι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0))
              inferInstance (n - (r : ℤ))
              (@CycleGroup.fundamental I.subscheme
                (LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ X.hom))
                ((I.subschemeι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0))
                (n - (r : ℤ)))) →
        ∃ θ : ChowCohomology.degree (fun _ ↦ 0) X'.hom ((r : ℤ) - 1),
          DirectSum.of (ChowCohomology.degree (fun _ ↦ 0) X'.hom) (r : ℤ)
              (ChowCohomology.restrictDegree (fun _ ↦ 0) b (r : ℤ)
                (BivariantClass.properPushforwardToTarget (fun _ ↦ 0)
                  (overHom (I.subschemeι ≫ X.hom) X.hom I.subschemeι rfl) (r : ℤ)
                  centerGysin)) =
            DirectSum.of (ChowCohomology.degree (fun _ ↦ 0) X'.hom)
              (1 + ((r : ℤ) - 1))
              (ChowCohomology.mul (fun _ ↦ 0) X'.hom
                (ChowCohomology.firstChernClass (fun _ ↦ 0) X'.hom
                  (I.comap b.left).associatedSheaf) θ) ∧
            ∀ n : ℤ,
              ChowGroup.map (fun _ ↦ 0)
                  (Over.mk ((I.comap b.left).subschemeι ≫ X'.hom))
                  (Over.mk (I.subschemeι ≫ X.hom))
                  (AlgebraicGeometry.IsBlowup.exceptionalProjectionOver I b)
                  ((n - ((r : ℤ) - 1)) - 1)
                  (ChowGroup.cartierGysin (fun _ ↦ 0) X' (I.comap b.left)
                    (n - ((r : ℤ) - 1))
                    (θ.cap (𝟙 X') (𝟙 X') (𝟙 X') IsPullback.of_id_snd n
                      (@chowClass X'.left
                        (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
                        (X'.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n
                        (@CycleGroup.fundamental X'.left
                          (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
                          (X'.hom.relativeDimensionFunction (fun _ ↦ 0)) n)))) =
                @chowClass I.subscheme
                  (LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ X.hom))
                  ((I.subschemeι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0))
                  inferInstance ((n - ((r : ℤ) - 1)) - 1)
                  (@CycleGroup.fundamental I.subscheme
                    (LocallyOfFiniteType.isLocallyNoetherian
                      (I.subschemeι ≫ X.hom))
                    ((I.subschemeι ≫ X.hom).relativeDimensionFunction (fun _ ↦ 0))
                    ((n - ((r : ℤ) - 1)) - 1)))
