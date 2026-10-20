module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NoetherianLocalMorphismProperty.Cancellation
import StacksCheckRecall

/-!
# Cancellation of local WAdm^Noeth morphism properties

A local property of continuous maps of Noetherian adic rings with cancellation
induces cancellation for morphisms of locally Noetherian formal algebraic spaces.
The source remark repeats the consequent and cites the composition lemma;
we use the cancellation implication and geometric variant established by the
immediately preceding cancellation situation, lemma, and proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing
open AlgebraicGeometry.IsFormalAlgebraicSpace
open AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

universe u v

/- Remark 87.21.18 (Variant for Noetherian): A local property of continuous maps
of Noetherian adic rings with cancellation induces cancellation for morphisms of
locally Noetherian formal algebraic spaces, in each equivalent local test. -/
@[stacks 0GBP] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.etaleAffineLocally.of_comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (g : Y ⟶ Z),
    Noetherian.IsLocalMorphismProperty P →
    Noetherian.HasCancellationProperty P →
    etaleAffineLocally P (f ≫ g) → etaleAffineLocally P g → etaleAffineLocally P f)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnTarget.of_comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (g : Y ⟶ Z),
    Noetherian.IsLocalMorphismProperty P →
    Noetherian.HasCancellationProperty P →
    existsCoverOnTarget P (f ≫ g) → existsCoverOnTarget P g → existsCoverOnTarget P f)

#check (AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian.existsCoverOnSource.of_comp :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop)
    (f : X ⟶ Y) (g : Y ⟶ Z),
    Noetherian.IsLocalMorphismProperty P →
    Noetherian.HasCancellationProperty P →
    existsCoverOnSource P (f ≫ g) → existsCoverOnSource P g → existsCoverOnSource P f)

#check (TopologicalRing.Noetherian.HasCancellationProperty :
  (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop) → Prop)

#check (TopologicalRing.Noetherian.HasCancellationProperty.of :
  ∀ (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop),
    (∀ {A B C : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
      [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
      (φ : B →+* A) (ψ : C →+* B),
      Continuous φ → Continuous ψ → P ψ → P (φ.comp ψ) → P φ) → Noetherian.HasCancellationProperty P)

#check (TopologicalRing.Noetherian.HasCancellationProperty.iff :
  ∀ (P : ∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
      (B →+* A) → Prop),
    Noetherian.HasCancellationProperty P ↔
    ∀ {A B C : Type u}
      [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
      [CommRing C] [TopologicalSpace C] [IsAdicRing C] [IsNoetherianRing C]
      (φ : B →+* A) (ψ : C →+* B),
      Continuous φ → Continuous ψ → P ψ → P (φ.comp ψ) → P φ)
