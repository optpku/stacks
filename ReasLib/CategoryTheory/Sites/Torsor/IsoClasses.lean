/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Torsor.Basic
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism classes of site torsors

This leaf owns the quotient-level torsor API used by cohomological classification statements.
The torsor itself remains the data owner in `Torsor.Basic`; this file adds only the canonical
isomorphism-class quotient, cover-triviality predicate, and the additive-to-multiplicative sheaf
bridge.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe w v u uι

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Torsor

variable {G : Sheaf J GrpCat.{w}}

/-- The type of isomorphism classes of `G`-torsors. -/
@[stacks 03AJ "isomorphism classes of torsors"]
abbrev IsoClasses (G : Sheaf J GrpCat.{w}) :=
  _root_.Quotient (Torsor.isomorphicSetoid G)

/-- An isomorphism of torsors preserves section existence over every site object. -/
theorem nonempty_sections_iff_of_iso {P Q : Torsor G} (e : Torsor.Iso P Q) (U : C) :
    Nonempty (P.Sections U) ↔ Nonempty (Q.Sections U) := sorry

namespace IsoClasses

variable {ι : Type uι} (V : ι → C)

/-- An isomorphism class of torsors is trivial on a family when every representative has a
section over every member of that family.  No covering hypothesis is built into this predicate. -/
@[stacks 0B8R "cover-trivial torsor classes"]
abbrev IsTrivialOnCover (c : Torsor.IsoClasses G) : Prop :=
  _root_.Quotient.liftOn c
    (fun P : Torsor G ↦ ∀ i : ι, Nonempty (P.Sections (V i)))
    (fun _ _ hPQ ↦ propext <|
      hPQ.elim fun e ↦
        forall_congr' fun i ↦ Torsor.nonempty_sections_iff_of_iso e (V i))

/-- The subset of torsor isomorphism classes which are trivial on every member of `V`. -/
@[stacks 0B8R "cover-trivial torsor classes"]
def trivialOnCover : Set (Torsor.IsoClasses G) :=
  {c | IsTrivialOnCover V c}

/-- Membership in `trivialOnCover` is the cover-triviality predicate. -/
@[simp, stacks 0B8R "cover-trivial torsor class membership"]
theorem mem_trivialOnCover_iff (c : Torsor.IsoClasses G) :
    c ∈ trivialOnCover V ↔ IsTrivialOnCover V c := sorry

/-- The image of cover-trivial torsor classes under an arbitrary class-valued map. -/
@[stacks 0B8R "image of cover-trivial torsor classes"]
def imageOnCover {β : Type*} (κ : Torsor.IsoClasses G → β) : Set β :=
  κ '' trivialOnCover V

/-- Membership in `imageOnCover` exposes its representing cover-trivial torsor class. -/
@[stacks 0B8R "cover-trivial torsor image membership"]
theorem mem_imageOnCover_iff {β : Type*} (κ : Torsor.IsoClasses G → β) {c : β} :
    c ∈ imageOnCover V κ ↔
      ∃ P : Torsor.IsoClasses G, IsTrivialOnCover V P ∧ κ P = c := sorry

/-- A representative torsor is trivial on `V` exactly when its quotient class is. -/
@[simp, stacks 0B8R "cover-trivial torsor quotient representative"]
theorem isTrivialOnCover_quot_mk_iff (P : Torsor G) :
    IsoClasses.IsTrivialOnCover V (_root_.Quotient.mk'' P : Torsor.IsoClasses G) ↔
      ∀ i : ι, Nonempty (P.Sections (V i)) := sorry

end IsoClasses
end Torsor

/-- The canonical equivalence witness for `AddCommGrpCat.toCommGrp` is available globally for
downstream sheaf-composition constructions. -/
instance toCommGrp_isEquivalence :
    AddCommGrpCat.toCommGrp.IsEquivalence :=
  commGroupAddCommGroupEquivalence.symm.isEquivalence_functor

variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]

/-- The canonical multiplicative sheaf associated to an additive sheaf. -/
@[stacks 03AJ "additive-to-multiplicative sheaf bridge"]
abbrev toSheafOfGroups (H : Sheaf J AddCommGrpCat.{max u v}) :
    Sheaf J GrpCat.{max u v} :=
  ((sheafCompose J AddCommGrpCat.toCommGrp) ⋙
    sheafCompose J (forget₂ CommGrpCat GrpCat)).obj H

/-- Read a section of the multiplicative presentation of an additive sheaf in its original
additive carrier. -/
@[stacks 03AJ "additive-to-multiplicative section readout"]
def toSheafOfGroupsValue (H : Sheaf J AddCommGrpCat.{max u v}) {U : Cᵒᵖ}
    (g : (toSheafOfGroups H).1.obj U) : H.1.obj U :=
  g

end Sheaf
end CategoryTheory
