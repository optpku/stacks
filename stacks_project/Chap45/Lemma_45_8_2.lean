/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FieldExtension.Colimit
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.FiniteIntermediate
public import ReasLib.Topology.Specialization.Dimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.FieldExtension
  AlgebraicGeometry.ChowGroup.FieldExtension

noncomputable section

universe u

namespace AlgebraicGeometry.ChowLimit

/-- The structure morphism `Spec K ⟶ Spec k` of a field extension. -/
abbrev algebraicExtensionStructureMap :=
  FieldExtension.specMap

/-- The constant-zero function on the spectrum of a field. -/
abbrev fieldDimension (F : Type u) [Field F] : Spec (CommRingCat.of F) → ℤ :=
  fun _ => 0

/-- The constant-zero function is a dimension function on the spectrum of a field. -/
def fieldDimension_isDimensionFunction (F : Type u) [Field F] :
    IsDimensionFunction (fieldDimension F) :=
  inferInstance

/-- The spectrum of a field is universally catenary. -/
def fieldSpec_universallyCatenary (F : Type u) [Field F] :
    UniversallyCatenary (Spec (CommRingCat.of F)) :=
  inferInstance

/-- The structure morphism of a field extension is flat. -/
def algebraicExtensionStructureMap_flat (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Flat (algebraicExtensionStructureMap k K) :=
  FieldExtension.specMap_flat k K

end AlgebraicGeometry.ChowLimit

/- Lemma 45.8.2: for an algebraic extension `K / k` and a finite-type `k`-scheme `X`,
the groups `CH_i(X_K)` are the filtered colimit of the groups `CH_i(X_L)` over finite
intermediate fields `L`. -/
@[stacks 0FH6]
#check (AlgebraicGeometry.ChowGroup.FieldExtension.finiteIntermediate_isFilteredColimit :
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) [Scheme.Hom.FiniteType X.hom] (i : ℤ)
    [Algebra.IsAlgebraic k K] (Y : AddCommGrpCat.{u})
    (f : ∀ L : FiniteIntermediateField k K, finiteIntermediateObject k K X i L ⟶ Y)
    (hf : ∀ {L M : FiniteIntermediateField k K} (h : L ≤ M),
      finiteIntermediateTransition k K X i h ≫ f M = f L),
    ∃! g :
      AddCommGrpCat.of
          (@ChowGroup.{u} (finiteIntermediateLimitBaseChange k K X).left
            (@LocallyOfFiniteType.isLocallyNoetherian
              (finiteIntermediateLimitBaseChange k K X).left
              (Spec (CommRingCat.of K))
              (finiteIntermediateLimitBaseChange k K X).hom inferInstance
              (@AlgebraicGeometry.instUniversallyCatenarySpec K _
                (@instUniversallyCatenaryRingOfField.{u, u} K _)).toIsLocallyNoetherian)
            ((finiteIntermediateLimitBaseChange k K X).hom.relativeDimensionFunction
              (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))) inferInstance i) ⟶
        Y,
      ∀ L : FiniteIntermediateField k K, finiteIntermediateLeg k K X i L ≫ g = f L)
