/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.QuasiCompact
public import ReasLib.CategoryTheory.Limits.Coproduct.Reindex
public import ReasLib.CategoryTheory.Sites.Sheaf.Types.Colimits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-compact objects in a sheaf topos

This is the topos-level companion to quasi-compact objects of a site.  It is expressed through
finite subcoproducts of locally surjective families and is independent of any textbook chapter.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type w)]

/-- Definition 7.17.4 (0D07) (1): a set-valued sheaf is quasi-compact when every locally
surjective coproduct presentation has a locally surjective finite subcoproduct. -/
@[stacks 0D07 "(1)", mk_iff isQuasiCompactObject_iff]
class IsQuasiCompactObject (F : Sheaf J (Type w)) : Prop where
  /-- A locally surjective coproduct presentation admits a finite locally surjective
  subpresentation. -/
  finiteSubcoproduct {ι : Type w} (Fᵢ : ι → Sheaf J (Type w)) [HasCoproduct Fᵢ]
      (π : (∐ Fᵢ) ⟶ F) (hπ : IsLocallySurjective π) :
      ∃ T : Set ι, T.Finite ∧
        IsLocallySurjective
          (Sigma.descReindex Fᵢ π (Subtype.val : T → ι))

end CategoryTheory.Sheaf

namespace CategoryTheory.GrothendieckTopology

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/- Definition 7.17.4 (0D07) (2): a sheaf topos is quasi-compact when its terminal sheaf is a
quasi-compact object. -/

/-- Definition 7.17.4 (0D07) (2): the sheaf topos presented by `J` is quasi-compact when its
terminal sheaf is a quasi-compact object. -/
@[stacks 0D07 "(2)"]
def IsQuasiCompact : Prop :=
  (⊤_ (Sheaf J (Type (max u v)))).IsQuasiCompactObject

end CategoryTheory.GrothendieckTopology
