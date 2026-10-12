/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import ReasLib.Algebra.Homology.CochainComplex.Admissible
public import ReasLib.Algebra.Homology.CochainComplex.Module
public import ReasLib.CategoryTheory.Filtration.Sequential

@[expose] public section

/-!
# Semi-Free Filtrations of Cochain Complexes

This leaf packages increasing filtrations of a cochain complex of modules
whose successive quotients are coproducts of shifted free complexes.  The
underlying sequential-colimit presentation belongs to the category-theory
filtration layer; this file adds the module-theoretic cell condition.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

/-- A semi-free filtration of a cochain complex of `A`-modules starts at zero, is degreewise
split along its consecutive inclusions, presents the ambient complex as its sequential colimit,
and has shifted-free successive quotients. -/
structure SemiFreeFiltration (P : CochainComplex (ModuleCat.{u, u} A) ℤ) where
  /-- The filtration stages. -/
  stage : ℕ → CochainComplex (ModuleCat.{u, u} A) ℤ
  /-- The consecutive inclusions of the filtration. -/
  inclusion : ∀ n : ℕ, stage n ⟶ stage (n + 1)
  /-- The initial stage is zero. -/
  stageZero : IsZero (stage 0)
  /-- The cocone from the filtration stages to the ambient complex. -/
  toCocone : Functor.ofSequence inclusion ⟶ (Functor.const ℕ).obj P
  /-- The supplied cocone is colimiting. -/
  isColimit : IsColimit (Cocone.mk P toCocone)
  /-- Consecutive inclusions are split after forgetting differentials. -/
  admissible : ∀ n : ℕ, IsAdmissibleMono (forgetToGraded (ModuleCat A)) (inclusion n)
  /-- The indexing type of shifted-free summands in each successive quotient. -/
  pieceIndex : ℕ → Type u
  /-- The shift of each free summand in a successive quotient. -/
  pieceDegree : ∀ n : ℕ, pieceIndex n → ℤ
  /-- The indicated coproduct of shifted-free summands exists. -/
  pieceHasCoproduct :
    ∀ n : ℕ, HasCoproduct (fun i : pieceIndex n ↦ shiftedFreeDGModule A (pieceDegree n i))
  /-- Each successive quotient is a coproduct of the indicated shifted-free summands. -/
  pieceIso :
    ∀ n : ℕ,
      let _ := pieceHasCoproduct n
      cokernel (inclusion n) ≅
        ∐ fun i : pieceIndex n ↦ shiftedFreeDGModule A (pieceDegree n i)

/-- A cochain complex of `A`-modules is semi-free when it admits a semi-free filtration. -/
def HasSemiFreeFiltration (P : CochainComplex (ModuleCat.{u, u} A) ℤ) : Prop :=
  Nonempty (SemiFreeFiltration P)

namespace SemiFreeFiltration

/-- Construct a semi-free filtration from an ordinary sequential-colimit presentation and the
successive shifted-free quotient data. -/
noncomputable def ofColimitIso {P : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (stage : ℕ → CochainComplex (ModuleCat.{u, u} A) ℤ)
    (inclusion : ∀ n : ℕ, stage n ⟶ stage (n + 1)) (stageZero : IsZero (stage 0))
    [HasColimit (Functor.ofSequence inclusion)]
    (colimitIso : P ≅ colimit (Functor.ofSequence inclusion))
    (admissible : ∀ n : ℕ, IsAdmissibleMono (forgetToGraded (ModuleCat A)) (inclusion n))
    (pieceIndex : ℕ → Type u) (pieceDegree : ∀ n : ℕ, pieceIndex n → ℤ)
    (pieceHasCoproduct : ∀ n : ℕ,
      HasCoproduct (fun i : pieceIndex n ↦ shiftedFreeDGModule A (pieceDegree n i)))
    (pieceIso : ∀ n : ℕ,
      let _ := pieceHasCoproduct n
      cokernel (inclusion n) ≅
        ∐ fun i : pieceIndex n ↦ shiftedFreeDGModule A (pieceDegree n i)) :
    SemiFreeFiltration P :=
  let F := SequentialColimitFiltration.ofColimitIso stage inclusion colimitIso
  { stage := stage
    inclusion := inclusion
    stageZero := stageZero
    toCocone := F.toCocone
    isColimit := F.isColimit
    admissible := admissible
    pieceIndex := pieceIndex
    pieceDegree := pieceDegree
    pieceHasCoproduct := pieceHasCoproduct
    pieceIso := pieceIso }

/-- The underlying sequential colimit filtration of a semi-free filtration. -/
def toSequentialColimitFiltration {P : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : SemiFreeFiltration P) : SequentialColimitFiltration P where
  stage := F.stage
  step := F.inclusion
  toCocone := F.toCocone
  isColimit := F.isColimit

/-- A semi-free filtration provides the colimit of its stage diagram. -/
instance instHasColimit {P : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : SemiFreeFiltration P) :
    HasColimit (Functor.ofSequence F.inclusion) :=
  F.toSequentialColimitFiltration.instHasColimit

/-- The chosen colimit data supplied by a semi-free filtration. -/
abbrev hasColimit {P : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : SemiFreeFiltration P) : HasColimit (Functor.ofSequence F.inclusion) :=
  F.instHasColimit

/-- Every consecutive inclusion in a semi-free filtration is monic. -/
theorem mono {P : CochainComplex (ModuleCat.{u, u} A) ℤ} (F : SemiFreeFiltration P) (n : ℕ) :
    Mono (F.inclusion n) := sorry

/-- Every consecutive inclusion in a semi-free filtration is split monic in each cochain degree.
-/
theorem stepTermwiseSplitMono {P : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : SemiFreeFiltration P) (k : ℕ) (n : ℤ) :
    IsSplitMono ((F.inclusion k).f n) := sorry

/-- The canonical comparison from the sequential colimit of the stages of a semi-free
filtration to its ambient cochain complex. -/
noncomputable def colimitComparison {P : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : SemiFreeFiltration P) :
    colimit (Functor.ofSequence F.inclusion) ≅ P :=
  F.toSequentialColimitFiltration.colimitComparison

/-- The ambient cochain complex of a semi-free filtration identifies with the colimit of its
stage diagram. -/
noncomputable def colimitIso {P : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : SemiFreeFiltration P) :
    P ≅ colimit (Functor.ofSequence F.inclusion) :=
  F.colimitComparison.symm

/-- Transport a semi-free filtration across an isomorphism of its ambient cochain complex. -/
noncomputable def transport {P Q : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : SemiFreeFiltration P) (e : P ≅ Q) :
    SemiFreeFiltration Q :=
  ofColimitIso F.stage F.inclusion F.stageZero (e.symm ≪≫ F.colimitIso) F.admissible
    F.pieceIndex F.pieceDegree F.pieceHasCoproduct F.pieceIso

/-- Transport preserves every filtration stage. -/
theorem transport_stage {P Q : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : SemiFreeFiltration P) (e : P ≅ Q) (n : ℕ) :
    (F.transport e).stage n = F.stage n := sorry

/-- Transport preserves every consecutive filtration map. -/
theorem transport_inclusion {P Q : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : SemiFreeFiltration P) (e : P ≅ Q) (n : ℕ) :
    (F.transport e).inclusion n = F.inclusion n := sorry

/-- The cocone map from a specified semi-free filtration stage to the ambient cochain complex. -/
abbrev coconeApp {P : CochainComplex (ModuleCat.{u, u} A) ℤ} (F : SemiFreeFiltration P)
    (n : ℕ) : F.stage n ⟶ P :=
  F.toCocone.app n

/-- The selected cocone map is the canonical colimit inclusion followed by the inverse of the
chosen colimit comparison. -/
theorem coconeApp_eq_colimitι_comp_colimitIso_inv
    {P : CochainComplex (ModuleCat.{u, u} A) ℤ} (F : SemiFreeFiltration P) (n : ℕ) :
    F.coconeApp n =
      colimit.ι (Functor.ofSequence F.inclusion) n ≫ F.colimitIso.inv :=
  (F.toSequentialColimitFiltration.colimit_ι_comp_colimitComparison_hom n).symm

/-- The cocone leg of a transported filtration is the original leg followed by the ambient
isomorphism. -/
theorem transport_coconeApp {P Q : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : SemiFreeFiltration P) (e : P ≅ Q) (n : ℕ) :
    (F.transport e).coconeApp n = F.coconeApp n ≫ e.hom := sorry

/-- A semi-free filtration exhibits the ambient cochain complex as semi-free. -/
theorem hasSemiFreeFiltration {P : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (F : SemiFreeFiltration P) :
    HasSemiFreeFiltration P := sorry

end SemiFreeFiltration

namespace HasSemiFreeFiltration

/-- Semi-free filtrations are invariant under isomorphisms of cochain complexes. -/
theorem ofIso {P Q : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (e : P ≅ Q) (hP : HasSemiFreeFiltration P) :
    HasSemiFreeFiltration Q := sorry

/-- Semi-free filtration existence is invariant under isomorphisms of cochain complexes. -/
theorem iff_ofIso {P Q : CochainComplex (ModuleCat.{u, u} A) ℤ} (e : P ≅ Q) :
    HasSemiFreeFiltration P ↔ HasSemiFreeFiltration Q := sorry

end HasSemiFreeFiltration

end CochainComplex
