/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree

@[expose] public section

/-!
# Finite Semi-Free Filtrations

This leaf packages finite-length and finite-support variants of semi-free
filtrations independently of any derived-category application.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CochainComplex.SemiFreeFiltration

variable {A : Type u} [Ring A]

/-- A finite cell filtration is a semi-free filtration that reaches its ambient complex after
finitely many stages and has finite quotient-index types before that stage. -/
structure FiniteCell (P : ModuleCat.DGMod A) extends SemiFreeFiltration P where
  /-- The last stage at which new cells occur. -/
  length : ℕ
  /-- The filtration reaches the ambient cochain complex at stage `length`. -/
  topIso : stage length ≅ P
  /-- Quotient-index types before the terminal stage are finite. -/
  pieceFintype : ∀ i : Fin length, Fintype (pieceIndex i)
  /-- No new quotient summands occur after the terminal stage. -/
  pieceIsEmpty : ∀ n : ℕ, length ≤ n → IsEmpty (pieceIndex n)

/-- A cochain complex has a finite cell filtration when it admits a `FiniteCell` structure. -/
def HasFiniteCellFiltration (P : ModuleCat.DGMod A) : Prop :=
  Nonempty (FiniteCell P)

namespace FiniteCell

/-- The quotient-index type at each nontrivial finite-cell stage is finite. -/
instance instPieceIndexFintype {P : ModuleCat.DGMod A}
    (F : FiniteCell P) (i : Fin F.length) :
    Fintype (F.pieceIndex i) :=
  F.pieceFintype i

/-- The consecutive maps of a finite cell filtration are monomorphisms. -/
instance instMonoInclusion {P : ModuleCat.DGMod A}
    (F : FiniteCell P) (n : ℕ) :
    Mono (F.inclusion n) :=
  F.toSemiFreeFiltration.mono n

/-- Transport a finite cell filtration across an isomorphism of ambient cochain complexes. -/
noncomputable def transport {P Q : ModuleCat.DGMod A}
    (F : FiniteCell P) (e : P ≅ Q) : FiniteCell Q :=
  { F.toSemiFreeFiltration.transport e with
    length := F.length
    topIso := F.topIso ≪≫ e
    pieceFintype := F.pieceFintype
    pieceIsEmpty := F.pieceIsEmpty }

/-- A finite cell filtration is in particular a semi-free filtration. -/
theorem hasSemiFreeFiltration {P : ModuleCat.DGMod A}
    (F : FiniteCell P) :
    HasSemiFreeFiltration P := sorry

end FiniteCell

namespace HasFiniteCellFiltration

/-- Finite cell filtrations are invariant under isomorphisms of cochain complexes. -/
theorem ofIso {P Q : ModuleCat.DGMod A} (e : P ≅ Q)
    (hP : HasFiniteCellFiltration P) :
    HasFiniteCellFiltration Q := sorry

/-- Finite cell filtration existence is invariant under isomorphisms of cochain complexes. -/
theorem iff_ofIso {P Q : ModuleCat.DGMod A} (e : P ≅ Q) :
    HasFiniteCellFiltration P ↔ HasFiniteCellFiltration Q := sorry

end HasFiniteCellFiltration

/-- A finite-support subfiltration of a semi-free filtration is a finite cell filtration of a
subobject together with compatible maps into each ambient stage and chosen finite subsets of the
ambient quotient summands. -/
structure FiniteSummandSubfiltration
    {P : ModuleCat.DGMod A} (F : SemiFreeFiltration P) where
  /-- The resulting cochain-complex subobject. -/
  subobject : Subobject P
  /-- The induced finite cell filtration on the chosen subobject. -/
  filtration : FiniteCell (Subobject.underlying.obj subobject)
  /-- The stagewise comparison into the ambient semi-free filtration. -/
  stageMap (n : ℕ) : filtration.stage n ⟶ F.stage n
  /-- The stagewise comparison maps commute with the consecutive inclusions. -/
  stageMap_comm (n : ℕ) :
    CommSq (filtration.inclusion n) (stageMap n) (stageMap (n + 1)) (F.inclusion n)
  /-- The top comparison lands in the ambient complex through the selected cocone map. -/
  stageMap_top :
    filtration.topIso.hom ≫ subobject.arrow =
      stageMap filtration.length ≫ F.coconeApp filtration.length
  /-- The quotient comparison induced at a nontrivial finite stage. -/
  quotientMap (i : Fin filtration.length) :
    cokernel (filtration.inclusion i.1) ⟶ cokernel (F.inclusion i.1)
  /-- The quotient comparison is induced by the next stage comparison. -/
  quotientMap_comm (i : Fin filtration.length) :
    CommSq (stageMap (i.1 + 1)) (cokernel.π (filtration.inclusion i.1))
      (cokernel.π (F.inclusion i.1)) (quotientMap i)
  /-- The retained summands at each finite stage form a subset of ambient summands. -/
  pieceSubset (i : Fin filtration.length) : Set (F.pieceIndex i)
  /-- The finite quotient summands are indexed by the chosen subset. -/
  pieceIndexEquiv (i : Fin filtration.length) : filtration.pieceIndex i ≃ pieceSubset i
  /-- Retained summands have the same shift degrees as their ambient counterparts. -/
  pieceDegree_eq (i : Fin filtration.length) (j : filtration.pieceIndex i) :
    filtration.pieceDegree i j = F.pieceDegree i (pieceIndexEquiv i j)

namespace FiniteSummandSubfiltration

/-- The cochain complex underlying a finite-support subfiltration. -/
abbrev obj {P : ModuleCat.DGMod A} {F : SemiFreeFiltration P}
    (F' : FiniteSummandSubfiltration F) : ModuleCat.DGMod A :=
  Subobject.underlying.obj F'.subobject

/-- Chosen retained-summand subsets are finite. -/
instance instPieceSubsetFintype {P : ModuleCat.DGMod A}
    {F : SemiFreeFiltration P} (F' : FiniteSummandSubfiltration F)
    (i : Fin F'.filtration.length) :
    Fintype (F'.pieceSubset i) :=
  Fintype.ofEquiv (F'.filtration.pieceIndex i) (F'.pieceIndexEquiv i)

/-- The ambient subobject selected by a finite-support subfiltration has a semi-free filtration. -/
theorem hasSemiFreeFiltration {P : ModuleCat.DGMod A}
    {F : SemiFreeFiltration P} (F' : FiniteSummandSubfiltration F) :
    HasSemiFreeFiltration F'.obj := sorry

end FiniteSummandSubfiltration

end CochainComplex.SemiFreeFiltration
