/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Abelian
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP

/-!
# Finite Property-P Filtrations

This leaf owns finite property-P filtrations, finite-cell filtrations, and chosen finite-summand
subfiltrations.  All submodules, comparison maps, retained summands, and degree identifications are
explicit data; only compatibility laws are propositions.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped DifferentialGradedModule

namespace DifferentialGradedModule.PropertyP

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/-- A finite property-P filtration reaches its ambient DG-module at a specified stage and has no
further cells.  Its earlier pieces may still be arbitrary coproducts of shifts of `A`. -/
@[stacks 09R2 "finite property-P filtration"]
structure FiniteFiltration (P : DifferentialGradedModule.{u, v} A) extends Filtration A P where
  /-- The stage at which the filtration reaches the ambient module. -/
  length : ℕ
  /-- The chosen identification of the terminal stage with the ambient module. -/
  topIso : stage length ≅ P
  /-- The terminal identification is the cocone map of the filtration. -/
  topIso_hom : topIso.hom = toFiltration.coconeApp length
  /-- No cells occur at or after the terminal stage. -/
  pieceIsEmpty : ∀ n : ℕ, length ≤ n → IsEmpty (pieceData n).index

/-- A finite-cell property-P filtration has only finitely many regular-module summands in every
successive piece. -/
@[stacks 09R3 "finite-cell property-P filtration"]
structure FiniteCell (P : DifferentialGradedModule.{u, v} A) extends FiniteFiltration A P where
  /-- Every nonterminal piece has a finite summand-index type. -/
  pieceFinite : ∀ i : Fin length, Finite (pieceData i).index

/-- DG-modules admitting a finite-cell property-P filtration. -/
@[stacks 09R3 "DG-modules with a finite-cell filtration"]
def HasFiniteCellFiltration : ObjectProperty (DifferentialGradedModule.{u, v} A) :=
  fun P ↦ Nonempty (FiniteCell A P)

namespace FiniteCell

/-- The summand-index type at every nonterminal finite-cell stage is finite. -/
@[stacks 09R3 "finite summand index at a finite-cell stage"]
instance instFinitePieceIndex {P : DifferentialGradedModule.{u, v} A}
    (F : FiniteCell A P) (i : Fin F.length) :
    Finite (F.pieceData i).index := sorry

/-- A finite-cell filtration exhibits its ambient module as having property P. -/
@[stacks 09R3 "a finite-cell filtration gives property P"]
theorem hasPropertyP {P : DifferentialGradedModule.{u, v} A}
    (F : FiniteCell A P) : DifferentialGradedModule.HasPropertyP A P := sorry

end FiniteCell

namespace HasFiniteCellFiltration

/-- Existence of a finite-cell filtration is invariant under isomorphism of DG-modules. -/
@[stacks 09R3 "finite-cell filtration existence is transported by isomorphism"]
theorem of_iso {P Q : DifferentialGradedModule.{u, v} A}
    (hP : HasFiniteCellFiltration A P) (e : P ≅ Q) :
    HasFiniteCellFiltration A Q := sorry

/-- An isomorphism identifies finite-cell filtration existence on its source and target. -/
@[stacks 09R3 "finite-cell filtration existence isomorphism criterion"]
theorem iff_of_iso {P Q : DifferentialGradedModule.{u, v} A} (e : P ≅ Q) :
    HasFiniteCellFiltration A P ↔ HasFiniteCellFiltration A Q := sorry

/-- Finite-cell filtration existence is closed under isomorphisms of DG-modules. -/
@[stacks 09R3 "finite-cell filtration isomorphism stability"]
instance isClosedUnderIsomorphisms :
    (HasFiniteCellFiltration A).IsClosedUnderIsomorphisms := sorry

end HasFiniteCellFiltration

/-- A finite-summand subfiltration records a DG-submodule, its finite-cell filtration, compatible
maps into the ambient stages, and the finite subsets of ambient summands retained at each stage. -/
@[stacks 09R2 "finite-summand subfiltration"]
structure FiniteSubfiltration {P : DifferentialGradedModule.{u, v} A}
    (F : Filtration A P) where
  /-- The DG-submodule selected by the finite subfiltration. -/
  subobject : Subobject P
  /-- The finite-cell filtration carried by the selected DG-submodule. -/
  filtration : FiniteCell A (Subobject.underlying.obj subobject)
  /-- The comparison from each selected filtration stage to the corresponding ambient stage. -/
  stageMap (n : ℕ) : filtration.stage n ⟶ F.stage n
  /-- Every selected stage is the pullback of the ambient stage along the subobject inclusion. -/
  stagePullback (n : ℕ) :
    IsPullback (stageMap n) (filtration.coconeApp n)
      (F.coconeApp n) subobject.arrow
  /-- Stage comparisons commute with the filtration steps. -/
  stageMap_comm (n : ℕ) :
    CommSq (filtration.step n) (stageMap n) (stageMap (n + 1)) (F.step n)
  /-- The terminal-stage comparison induces the selected subobject arrow. -/
  stageMap_top :
    filtration.topIso.hom ≫ subobject.arrow =
      stageMap filtration.length ≫ F.coconeApp filtration.length
  /-- The comparison between successive pieces. -/
  pieceMap (i : Fin filtration.length) : filtration.piece i ⟶ F.piece i
  /-- Successive-piece comparisons commute with the quotient projections. -/
  pieceMap_comm (i : Fin filtration.length) :
    CommSq (stageMap (i + 1)) (filtration.projection i)
      (F.projection i) (pieceMap i)
  /-- The ambient summands retained at a finite stage. -/
  pieceSubset (i : Fin filtration.length) : Set (F.pieceData i).index
  /-- The selected piece summands are indexed by the retained ambient subset. -/
  pieceIndexEquiv (i : Fin filtration.length) :
    (filtration.pieceData i).index ≃ pieceSubset i
  /-- A retained summand has the same shift degree as its ambient summand. -/
  pieceDegree_eq (i : Fin filtration.length) (j : (filtration.pieceData i).index) :
    (filtration.pieceData i).degree j =
      (F.pieceData i).degree (pieceIndexEquiv i j)
  /-- The piece comparison is induced by the retained ambient summands. -/
  pieceMap_ι (i : Fin filtration.length) (j : (filtration.pieceData i).index) :
    (filtration.pieceData i).ι j ≫ pieceMap i =
      (filtration.pieceData i).summandEqToHom (F.pieceData i)
          j (pieceIndexEquiv i j) (pieceDegree_eq i j) ≫
        (F.pieceData i).ι (pieceIndexEquiv i j)

namespace FiniteSubfiltration

/-- The DG-module underlying a finite-summand subfiltration. -/
@[stacks 09R2 "underlying DG-module of a finite subfiltration"]
abbrev obj {P : DifferentialGradedModule.{u, v} A} {F : Filtration A P}
    (F' : FiniteSubfiltration A F) : DifferentialGradedModule.{u, v} A :=
  Subobject.underlying.obj F'.subobject

/-- The retained ambient summands at every finite stage form a finite type. -/
@[stacks 09R2 "finite retained summand type"]
instance instFinitePieceSubset {P : DifferentialGradedModule.{u, v} A}
    {F : Filtration A P} (F' : FiniteSubfiltration A F)
    (i : Fin F'.filtration.length) : Finite (F'.pieceSubset i) := sorry

/-- The retained summand subset at each nonterminal stage is finite. -/
@[stacks 09R2 "finiteness of retained finite-subfiltration summands"]
theorem pieceSubset_finite {P : DifferentialGradedModule.{u, v} A}
    {F : Filtration A P} (F' : FiniteSubfiltration A F)
    (i : Fin F'.filtration.length) : F'.pieceSubset i |>.Finite := sorry

/-- The selected DG-submodule has a finite-cell filtration. -/
@[stacks 09R3 "finite-cell filtration of a selected subfiltration"]
theorem hasFiniteCellFiltration {P : DifferentialGradedModule.{u, v} A}
    {F : Filtration A P} (F' : FiniteSubfiltration A F) :
    HasFiniteCellFiltration A F'.obj := sorry

end FiniteSubfiltration

#synth (HasFiniteCellFiltration A).IsClosedUnderIsomorphisms

end DifferentialGradedModule.PropertyP
