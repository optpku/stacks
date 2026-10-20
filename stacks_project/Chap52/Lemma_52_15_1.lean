module

public import stacks_project.Chap52.Lemma_52_15_1_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

variable {X : Scheme.{u}} [IsNoetherian X]

/- Lemma 52.15.1 (1): quasi-affineness and completeness of the structure sheaf imply
eventual completeness of the nonnegative tensor powers of an ample invertible module. -/
@[stacks 0EKP] #check (AlgebraicGeometry.Scheme.CoherentCompletion.quasiAffine_implies_hasAmple :
  {X : Scheme.{u}} → [IsNoetherian X] → (I : X.IdealSheafData) →
    (hX : X.IsQuasiAffine) →
    (h_complete : Function.Bijective
      (sectionsComparison I (SheafOfModules.unit X.ringCatSheaf))) →
    ∃ L : X.Modules, Modules.isAmpleObject L ∧
      ∃ m₀ : ℕ, ∀ m ≥ m₀,
        Function.Bijective
          (sectionsComparison I (RingedSpace.TensorPower.sheaf L m)))

/- Lemma 52.15.1 (2): eventual completeness of the nonnegative tensor powers of an ample
invertible module implies completeness of every finite locally free coherent module. -/
@[stacks 0EKP] #check (AlgebraicGeometry.Scheme.CoherentCompletion.hasAmple_implies_finiteLocallyFree :
  {X : Scheme.{u}} → [IsNoetherian X] → (I : X.IdealSheafData) → (L : X.Modules) →
    (hL : Modules.isAmpleObject L) →
    (h_complete : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      Function.Bijective
        (sectionsComparison I (RingedSpace.TensorPower.sheaf L m))) →
    ∀ E : RingedSpace.Coh X.toRingedSpace, finiteLocallyFree X E →
      Function.Bijective (sectionsComparison I E.obj))

/- Lemma 52.15.1 (3): completeness of every finite locally free coherent module implies
full faithfulness of completion on the corresponding full subcategory. -/
@[stacks 0EKP] #check (AlgebraicGeometry.Scheme.CoherentCompletion.finiteLocallyFree_implies_fullyFaithful :
  {X : Scheme.{u}} → [IsNoetherian X] → (I : X.IdealSheafData) →
    (h_complete : ∀ E : RingedSpace.Coh X.toRingedSpace, finiteLocallyFree X E →
      Function.Bijective (sectionsComparison I E.obj)) →
    Nonempty (onFiniteLocallyFree I).FullyFaithful)

/- Lemma 52.15.1 (4): full faithfulness of completion on finite locally free coherent modules
implies completeness of every such module. -/
@[stacks 0EKP] #check (AlgebraicGeometry.Scheme.CoherentCompletion.fullyFaithful_implies_finiteLocallyFree :
  {X : Scheme.{u}} → [IsNoetherian X] → (I : X.IdealSheafData) →
    (h_fully_faithful : Nonempty (onFiniteLocallyFree I).FullyFaithful) →
    ∀ E : RingedSpace.Coh X.toRingedSpace, finiteLocallyFree X E →
      Function.Bijective (sectionsComparison I E.obj))

end AlgebraicGeometry.Scheme.CoherentCompletion
