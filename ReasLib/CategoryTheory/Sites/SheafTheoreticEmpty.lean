/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.SheafTheoreticEmpty.Sections
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
public import Mathlib.Data.List.TFAE

/-!
# Sheaf-theoretically empty objects

An object of a site is sheaf-theoretically empty when its sheafified representable is initial.
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

open scoped SheafifiedRepresentable

/-- The sheafification of the initial `Type (max u v)`-valued presheaf.

It is the canonical test object for the bottom-sieve criterion. -/
noncomputable abbrev sheafifyInitial (J : GrothendieckTopology C) :
    Cᵒᵖ ⥤ Type (max u v) :=
  J.sheafify (⊥_ (Cᵒᵖ ⥤ Type (max u v)))

namespace IsSheafTheoreticallyEmpty

/-- A sheaf-theoretically empty object supplies an initiality witness for its sheafified
representable. -/
theorem nonempty_isInitial {J : GrothendieckTopology C} {U : C}
    (hU : J.IsSheafTheoreticallyEmpty U) :
    Nonempty (IsInitial h[U]^#[J]) := sorry

end IsSheafTheoreticallyEmpty

/-- An object is sheaf-theoretically empty exactly when its sheafified
representable is initial. -/
@[stacks 04B5]
theorem isSheafTheoreticallyEmpty_iff_nonempty_isInitial
    (J : GrothendieckTopology C) (U : C) :
    J.IsSheafTheoreticallyEmpty U ↔ Nonempty (IsInitial h[U]^#[J]) := sorry

/-- A sheaf-theoretically empty object is characterized by unique sections of every
set-valued sheaf. -/
theorem isSheafTheoreticallyEmpty_iff_forall_unique_sections
    (J : GrothendieckTopology C) (U : C) :
    J.IsSheafTheoreticallyEmpty U ↔
      ∀ ℱ : Sheaf J (Type (max u v)), Nonempty (Unique (ℱ.obj.obj (op U))) := sorry

/-- A sheaf-theoretically empty object is characterized by the existence of a section of the
sheafification of the initial presheaf. -/
@[stacks 04B6]
theorem isSheafTheoreticallyEmpty_iff_sheafifyInitial_nonempty
    (J : GrothendieckTopology C) (U : C) :
    J.IsSheafTheoreticallyEmpty U ↔ Nonempty ((J.sheafifyInitial).obj (op U)) := sorry

/-- A sheaf-theoretically empty object is characterized by unique sections of the sheafification
of the initial presheaf. -/
@[stacks 04B6]
theorem isSheafTheoreticallyEmpty_iff_sheafifyInitial_unique
    (J : GrothendieckTopology C) (U : C) :
    J.IsSheafTheoreticallyEmpty U ↔
      Nonempty (Unique ((J.sheafifyInitial).obj (op U))) := sorry

/-- Lemma 7.42.2 (04B6): sheaf theoretical emptiness, unique sections of every sheaf, nonempty
sections of the sheafification of the initial presheaf, and coverage of the bottom sieve are
equivalent. -/
@[stacks 04B6]
theorem isSheafTheoreticallyEmpty_tfae (J : GrothendieckTopology C) (U : C) :
    List.TFAE
      [ J.IsSheafTheoreticallyEmpty U,
        ∀ ℱ : Sheaf J (Type (max u v)), Nonempty (Unique (ℱ.obj.obj (op U))),
        Nonempty (Unique ((J.sheafifyInitial).obj (op U))),
        Nonempty ((J.sheafifyInitial).obj (op U)),
        (⊥ : Sieve U) ∈ J U ] := sorry

end CategoryTheory.GrothendieckTopology
