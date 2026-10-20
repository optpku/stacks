module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local properties of tensor powers

These instances attach the standard local finiteness and freeness predicates directly to the
tensor-power owner.  Consumers can therefore use typeclass search instead of replaying an
induction on the degree.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.TensorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}
variable (F : ringedSiteModuleCategory.{u, v, w, w} J 𝒪) (n : ℕ)

section OneLevel

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Lemma 17.21.5 (1) (01CK), tensor power: tensor powers preserve local generation by
sections. -/
@[stacks 01CK "(1), tensor power"]
instance isLocallyGeneratedBySections
    [IsLocallyGeneratedBySections F] :
    IsLocallyGeneratedBySections (sheaf 𝒪 F n) := sorry

/-- Lemma 17.21.5 (2) (01CK), tensor power: tensor powers preserve finite type. -/
@[stacks 01CK "(2), tensor power"]
instance isFiniteType [F.IsFiniteType] : (sheaf 𝒪 F n).IsFiniteType := sorry

/-- Lemma 17.21.5 (3) (01CK), tensor power: tensor powers preserve finite presentation. -/
@[stacks 01CK "(3), tensor power"]
instance isFinitePresentation [F.IsFinitePresentation] :
    (sheaf 𝒪 F n).IsFinitePresentation := sorry

/-- Lemma 17.21.5 (5) (01CK), tensor power: tensor powers preserve quasi-coherence. -/
@[stacks 01CK "(5), tensor power"]
instance isQuasicoherent [F.IsQuasicoherent] :
    (sheaf 𝒪 F n).IsQuasicoherent := sorry

/-- Lemma 17.21.5 (6) (01CK), tensor power: tensor powers preserve local freeness. -/
@[stacks 01CK "(6), tensor power"]
instance isLocallyFree [F.IsLocallyFree] : (sheaf 𝒪 F n).IsLocallyFree := sorry

/-- Lemma 17.21.5 (01CK), tensor power: tensor powers preserve finite local freeness. -/
@[stacks 01CK "finite locally free tensor power"]
instance isFiniteLocallyFree [F.IsFiniteLocallyFree] :
    IsFiniteLocallyFree (sheaf 𝒪 F n) := sorry

/-- The `n`th tensor power of a finite locally free module sheaf of rank `r` is finite locally
free of rank `r ^ n`. -/
@[stacks 01CK "tensor power rank formula"]
instance isFiniteLocallyFreeOfRank (r : ℕ) [IsFiniteLocallyFreeOfRank r F] :
    IsFiniteLocallyFreeOfRank (r ^ n) (sheaf 𝒪 F n) := sorry

end OneLevel

section Iterated

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ (U : C) (V : Over U),
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ (U : C) (V : Over U),
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Lemma 17.21.5 (4) (01CK), tensor power: every positive tensor power of a coherent module
sheaf is coherent. -/
@[stacks 01CK "(4), tensor power"]
instance isCoherent_succ [IsCoherent F] :
    IsCoherent (sheaf 𝒪 F (n + 1)) := sorry

end Iterated

end SheafOfModules.RingedSite.TensorPower
