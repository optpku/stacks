/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import ReasLib.AlgebraicGeometry.GroupScheme
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupScheme

/-- A group-valued Zariski sheaf on schemes over a field is represented by a group scheme if it
contains a representable relatively open subfunctor whose translates by rational points meet every
field-valued point. -/
@[stacks 0B9Q]
theorem representable_of_openSubfunctor
    {k : Type u} [Field k] (G : (SchemeOverField k)ᵒᵖ ⥤ GrpCat.{u})
    (F : Subfunctor (G ⋙ forget GrpCat))
    (h_sheaf : Presheaf.IsSheaf
      (Scheme.zariskiTopology.over (Spec (CommRingCat.of k))) (G ⋙ forget GrpCat))
    (h_representable : F.toFunctor.IsRepresentable)
    (h_open : ((@IsOpenImmersion).inverseImage
      (Over.forget (Spec (CommRingCat.of k)))).presheaf F.ι)
    (h_fieldPoints : ∀ (K : Type u) [Field K] [Algebra k K]
      (g : G.obj (op (Over.mk (FieldExtension.specMap k K)))),
      ∃ g' : G.obj (op (⊤_ SchemeOverField k)),
        G.map (terminal.from (Over.mk (FieldExtension.specMap k K))).op g' * g ∈
          F.obj (op (Over.mk (FieldExtension.specMap k K)))) :
    (yonedaGrp : GroupScheme (Spec (CommRingCat.of k)) ⥤
      (SchemeOverField k)ᵒᵖ ⥤ GrpCat.{u}).essImage G := sorry

end AlgebraicGeometry.GroupScheme
