module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Over

/-!
# Chow groups and envelopes

This file defines the descent complex associated to a proper morphism and states its
exactness for envelopes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Descent

variable {S X Y : Scheme.{u}}

/-- The self-pullback of `f`, regarded over `S` through its first projection. -/
abbrev relation (p : X ⟶ S) (f : Y ⟶ X) : Over S :=
  Over.mk (pullback.fst f f ≫ f ≫ p)

/-- The underlying scheme of the descent relation is the self-pullback of `f`. -/
theorem relation_left (p : X ⟶ S) (f : Y ⟶ X) :
    (relation p f).left = pullback f f := sorry

/-- The structure morphism of the descent relation is induced by the first projection. -/
theorem relation_hom (p : X ⟶ S) (f : Y ⟶ X) :
    (relation p f).hom = pullback.fst f f ≫ f ≫ p := sorry

/-- The morphism `f` commutes with the structure morphisms over `S`. -/
theorem augmentation_comp (p : X ⟶ S) (f : Y ⟶ X) :
    f ≫ (Over.mk p).hom = (Over.mk (f ≫ p)).hom := sorry

/-- The augmentation from `Y` over `S` to `X` over `S`. -/
abbrev augmentation (p : X ⟶ S) (f : Y ⟶ X) :
    Over.mk (f ≫ p) ⟶ Over.mk p :=
  Over.homMk f (augmentation_comp p f)

/-- The underlying scheme morphism of the augmentation is `f`. -/
theorem augmentation_left (p : X ⟶ S) (f : Y ⟶ X) :
    (augmentation p f).left = f := sorry

/-- The first pullback projection commutes with the structure morphisms over `S`. -/
theorem fst_comp (p : X ⟶ S) (f : Y ⟶ X) :
    pullback.fst f f ≫ (Over.mk (f ≫ p)).hom = (relation p f).hom := sorry

/-- The first projection from the descent relation to `Y` over `S`. -/
abbrev fst (p : X ⟶ S) (f : Y ⟶ X) :
    relation p f ⟶ Over.mk (f ≫ p) :=
  Over.homMk (pullback.fst f f) (fst_comp p f)

/-- The underlying scheme morphism of the first projection is `pullback.fst f f`. -/
theorem fst_left (p : X ⟶ S) (f : Y ⟶ X) :
    (fst p f).left = pullback.fst f f := sorry

/-- The second pullback projection commutes with the structure morphisms over `S`. -/
theorem snd_comp (p : X ⟶ S) (f : Y ⟶ X) :
    pullback.snd f f ≫ (Over.mk (f ≫ p)).hom = (relation p f).hom := sorry

/-- The second projection from the descent relation to `Y` over `S`. -/
abbrev snd (p : X ⟶ S) (f : Y ⟶ X) :
    relation p f ⟶ Over.mk (f ≫ p) :=
  Over.homMk (pullback.snd f f) (snd_comp p f)

/-- The underlying scheme morphism of the second projection is `pullback.snd f f`. -/
theorem snd_left (p : X ⟶ S) (f : Y ⟶ X) :
    (snd p f).left = pullback.snd f f := sorry

/-- The difference of proper pushforwards along the two projections of a self-pullback. -/
noncomputable def projectionDifference
    (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (f : Y ⟶ X) [IsProper f] (k : ℤ) :
    @ChowGroup (relation p f).left
        (LocallyOfFiniteType.isLocallyNoetherian (relation p f).hom)
        ((relation p f).hom.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup (Over.mk (f ≫ p)).left
        (LocallyOfFiniteType.isLocallyNoetherian (Over.mk (f ≫ p)).hom)
        ((Over.mk (f ≫ p)).hom.relativeDimensionFunction δ) inferInstance k :=
  ChowGroup.map δ (relation p f) (Over.mk (f ≫ p)) (fst p f) k -
    @ChowGroup.map S inferInstance δ inferInstance (relation p f) (Over.mk (f ≫ p))
      inferInstance inferInstance (snd p f)
      (Eq.mpr (congrArg IsProper (snd_left p f))
        (inferInstance : IsProper (pullback.snd f f))) k

/-- The projection-difference map is first pushforward minus second pushforward. -/
theorem projectionDifference_apply
    (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (f : Y ⟶ X) [IsProper f] (k : ℤ)
    (α : @ChowGroup (relation p f).left
      (LocallyOfFiniteType.isLocallyNoetherian (relation p f).hom)
      ((relation p f).hom.relativeDimensionFunction δ) inferInstance k) :
    projectionDifference p δ f k α =
      ChowGroup.map δ (relation p f) (Over.mk (f ≫ p)) (fst p f) k α -
        @ChowGroup.map S inferInstance δ inferInstance (relation p f) (Over.mk (f ≫ p))
          inferInstance inferInstance (snd p f)
          (Eq.mpr (congrArg IsProper (snd_left p f))
            (inferInstance : IsProper (pullback.snd f f))) k α := sorry

/-- Projection difference followed by augmentation pushforward is zero. -/
theorem projectionDifference_comp
    (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (f : Y ⟶ X) [IsProper f] (k : ℤ) :
    AddCommGrpCat.ofHom (projectionDifference p δ f k) ≫
      AddCommGrpCat.ofHom
        (ChowGroup.map δ (Over.mk (f ≫ p)) (Over.mk p) (augmentation p f) k) = 0 := sorry

/-- The augmented descent short complex on degree-`k` Chow groups associated to `f`. -/
noncomputable def complex
    (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (f : Y ⟶ X) [IsProper f]
    (k : ℤ) : ShortComplex Ab :=
  ShortComplex.mk (AddCommGrpCat.ofHom (projectionDifference p δ f k))
    (AddCommGrpCat.ofHom
      (ChowGroup.map δ (Over.mk (f ≫ p)) (Over.mk p) (augmentation p f) k))
    (projectionDifference_comp p δ f k)

/-- The first arrow of the descent complex is the projection-difference pushforward. -/
theorem complex_f
    (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (f : Y ⟶ X) [IsProper f] (k : ℤ) :
    (complex p δ f k).f = AddCommGrpCat.ofHom (projectionDifference p δ f k) := sorry

/-- The second arrow of the descent complex is pushforward along `f`. -/
theorem complex_g
    (p : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType p]
    (δ : S → ℤ) [IsDimensionFunction δ] (f : Y ⟶ X) [IsProper f] (k : ℤ) :
    (complex p δ f k).g = AddCommGrpCat.ofHom
      (ChowGroup.map δ (Over.mk (f ≫ p)) (Over.mk p) (augmentation p f) k) := sorry

end AlgebraicGeometry.ChowGroup.Descent

namespace AlgebraicGeometry.ChowGroup.Envelope

/-- The descent complex of an envelope is exact at its middle Chow group, and its
augmentation is an epimorphism. -/
theorem exact {S X Y : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
    (f : Y ⟶ X) [IsEnvelope f] (k : ℤ) :
    (Descent.complex p δ f k).Exact ∧ Epi (Descent.complex p δ f k).g := sorry

end AlgebraicGeometry.ChowGroup.Envelope
