/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.QuasiCompact
public import ReasLib.CategoryTheory.Sites.QuasiCompact.Sheaf
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-!
# Quasi-compact sheaves and representables

This file connects quasi-compact site objects with sheafified representables,
and records the locally-surjective descent principle for quasi-compact sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Sheaf.IsQuasiCompactObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

/-- Quasi-compact sheaves are closed under categorical quotients. -/
instance isClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (IsQuasiCompactObject : ObjectProperty (Sheaf J (Type (max u v)))) := sorry

/-- Lemma 7.17.5 (0GMP) (2): a locally surjective image of a quasi-compact sheaf of
sets is quasi-compact. -/
@[stacks 0GMP "(2)"]
theorem of_locallySurjective
    {F G : Sheaf J (Type (max u v))} (π : F ⟶ G)
    (hπ : IsLocallySurjective π) (hF : F.IsQuasiCompactObject) :
    G.IsQuasiCompactObject := sorry

end CategoryTheory.Sheaf.IsQuasiCompactObject

namespace CategoryTheory.GrothendieckTopology.QuasiCompactObject

open CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

/-- Lemma 7.17.3 (0D06): a site object is quasi-compact exactly when its
sheafified representable is quasi-compact. -/
@[stacks 0D06]
theorem sheafifiedRepresentable_iff (U : C) :
    J.QuasiCompactObject U ↔ (J.sheafifiedRepresentable U).IsQuasiCompactObject := sorry

/-- Lemma 7.17.5 (0GMP) (1): a locally-surjective sheafified-representable map
transports quasi-compactness to its target site object. -/
@[stacks 0GMP "(1)"]
theorem of_sheafifiedRepresentableMap
    {U V : C} (f : U ⟶ V)
    (hf : IsLocallySurjective (J.sheafifiedRepresentableMap f))
    (hU : J.QuasiCompactObject U) :
    J.QuasiCompactObject V := sorry

end CategoryTheory.GrothendieckTopology.QuasiCompactObject
