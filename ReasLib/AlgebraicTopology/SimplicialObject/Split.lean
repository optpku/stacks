module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 016F

# Split face and degeneracy morphisms

The simplicial identities canonically split every face and degeneracy morphism. This file records
chosen split-epi and split-mono data for simplicial and cosimplicial objects and registers the
corresponding instances for downstream typeclass search.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace δ

/-- The selected section of a face morphism: use the degeneracy with the same index, except at
the final face, where the final degeneracy is used. -/
@[stacks 016F "canonical section of a face"]
def section_ (U : SimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    U.obj (Opposite.op (SimplexCategory.mk n)) ⟶
      U.obj (Opposite.op (SimplexCategory.mk (n + 1))) :=
  Fin.lastCases (U.σ (Fin.last n)) (fun j ↦ U.σ j) i

/-- The selected section of a face followed by that face is the identity. -/
@[stacks 016F "canonical section identity for a face"]
theorem section_comp (U : SimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    section_ U i ≫ U.δ i = 𝟙 (U.obj (Opposite.op (SimplexCategory.mk n))) := sorry

/-- A face morphism of a simplicial object has a selected split-epi structure coming from an
adjacent degeneracy. -/
@[stacks 016F "canonical split-epi structure on faces"]
def splitEpi (U : SimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    SplitEpi (U.δ i) :=
  SplitEpi.mk (section_ U i) (section_comp U i)

/-- Face morphisms of simplicial objects are canonically split epimorphisms. -/
@[stacks 016F "canonical split-epi instance on faces"]
instance isSplitEpi (U : SimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    IsSplitEpi (U.δ i) :=
  IsSplitEpi.mk' (splitEpi U i)

end δ

namespace σ

/-- The selected retraction of a degeneracy is the face with the same index. -/
@[stacks 016F "canonical retraction of a degeneracy"]
def retraction (U : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    U.obj (Opposite.op (SimplexCategory.mk (n + 1))) ⟶
      U.obj (Opposite.op (SimplexCategory.mk n)) :=
  U.δ i.castSucc

/-- A degeneracy followed by its selected retraction is the identity. -/
@[stacks 016F "canonical retraction identity for a degeneracy"]
theorem comp_retraction (U : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    U.σ i ≫ retraction U i =
      𝟙 (U.obj (Opposite.op (SimplexCategory.mk n))) := sorry

/-- A degeneracy morphism has its adjacent face morphism as a canonical retraction. -/
@[stacks 016F]
def splitMono (U : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    SplitMono (U.σ i) :=
  SplitMono.mk (retraction U i) (comp_retraction U i)

/-- Degeneracy morphisms of simplicial objects are canonically split monomorphisms. -/
@[stacks 016F "canonical split-mono structure on degeneracies"]
instance isSplitMono (U : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    IsSplitMono (U.σ i) :=
  IsSplitMono.mk' (splitMono U i)

end σ

end CategoryTheory.SimplicialObject

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

namespace σ

/-- The selected section of a codegeneracy is the coface with the same index. -/
@[stacks 016O "canonical section of a codegeneracy"]
def section_ (U : CosimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    U.obj (SimplexCategory.mk n) ⟶ U.obj (SimplexCategory.mk (n + 1)) :=
  U.δ i.castSucc

/-- The selected section of a codegeneracy followed by that codegeneracy is the identity. -/
@[stacks 016O "canonical section identity for a codegeneracy"]
theorem section_comp (U : CosimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    section_ U i ≫ U.σ i = 𝟙 (U.obj (SimplexCategory.mk n)) := sorry

/-- A codegeneracy morphism of a cosimplicial object has its canonical split-epi structure. -/
@[stacks 016O "canonical split-epi structure on codegeneracies"]
def splitEpi (U : CosimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    SplitEpi (U.σ i) :=
  SplitEpi.mk (section_ U i) (section_comp U i)

/-- Codegeneracy morphisms of cosimplicial objects are canonically split epimorphisms. -/
@[stacks 016O "canonical split-epi instance on codegeneracies"]
instance isSplitEpi (U : CosimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    IsSplitEpi (U.σ i) :=
  IsSplitEpi.mk' (splitEpi U i)

end σ

namespace δ

/-- The selected retraction of a coface morphism: use the codegeneracy with the same index,
except at the final coface, where the final codegeneracy is used. -/
@[stacks 016O "canonical retraction of a coface"]
def retraction (U : CosimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    U.obj (SimplexCategory.mk (n + 1)) ⟶ U.obj (SimplexCategory.mk n) :=
  Fin.lastCases (U.σ (Fin.last n)) (fun j ↦ U.σ j) i

/-- A coface followed by its selected retraction is the identity. -/
@[stacks 016O "canonical retraction identity for a coface"]
theorem comp_retraction (U : CosimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    U.δ i ≫ retraction U i = 𝟙 (U.obj (SimplexCategory.mk n)) := sorry

/-- A coface morphism has a selected split-monomorphism structure coming from an adjacent
codegeneracy. -/
@[stacks 016O]
def splitMono (U : CosimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    SplitMono (U.δ i) :=
  SplitMono.mk (retraction U i) (comp_retraction U i)

/-- Coface morphisms of cosimplicial objects are canonically split monomorphisms. -/
@[stacks 016O "canonical split-mono structure on cofaces"]
instance isSplitMono (U : CosimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    IsSplitMono (U.δ i) :=
  IsSplitMono.mk' (splitMono U i)

end δ

end CategoryTheory.CosimplicialObject
