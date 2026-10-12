/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom
public import ReasLib.CategoryTheory.Sites.Cover.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Cover maps between sheafified representables

This module owns the canonical map from the coproduct of the sheafified
representables attached to a cover to the sheafified representable of its target.
It is independent of the numbered site-theory development.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open GrothendieckTopology.Cover

universe w u v

namespace CategoryTheory.GrothendieckTopology

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The canonical map from the sheafified representables of a cover to that of its target. -/
abbrev sheafifiedRepresentableCoverMap [HasWeakSheafify J (Type (max u v))]
    {U : C} (S : J.Cover U) :
    (∐ fun I : S.Arrow => J.sheafifiedRepresentable I.Y) ⟶
      J.sheafifiedRepresentable U :=
  Limits.Sigma.desc (fun I : S.Arrow => J.sheafifiedRepresentableMap I.f)

/-- Local surjectivity of a coproduct map of sheafified representables is equivalent to that of
the corresponding presheaf coproduct map. -/
theorem isLocallySurjective_sigmaDesc_sheafifiedRepresentableMap_iff
    [HasWeakSheafify J (Type (max u v))]
    {ι : Type*} [Small.{max u v} ι] {U : C} (Y : ι -> C) (f : forall i : ι, Y i ⟶ U)
    [HasCoproduct (fun i : ι => J.sheafifiedRepresentable (Y i))] :
    Sheaf.IsLocallySurjective
        (Limits.Sigma.desc (fun i : ι => J.sheafifiedRepresentableMap (f i))) <->
      Presheaf.IsLocallySurjective J
        (Limits.Sigma.desc (fun i : ι => CategoryTheory.uliftYoneda.{max u v}.map (f i))) := sorry

variable {J}
variable {U : C} (S : J.Cover U)

/-- Sections of a sheaf over a covered object are determined by their restrictions to the cover. -/
lemma section_eq_of_cover_restrictions_eq
    {F : Sheaf J (Type (max u v))} {s t : F.obj.obj (op U)}
    (h : forall I : S.Arrow, F.obj.map I.f.op s = F.obj.map I.f.op t) :
    s = t := sorry

/-- Equality after precomposition with a canonical cover map gives equality on every cover
component. -/
lemma cover_component_eq_of_coverMap_comp_eq
    [HasWeakSheafify J (Type (max u v))]
    {F : Sheaf J (Type (max u v))} {alpha beta : J.sheafifiedRepresentable U ⟶ F}
    (h : sheafifiedRepresentableCoverMap J S ≫ alpha =
      sheafifiedRepresentableCoverMap J S ≫ beta) :
    forall I : S.Arrow,
      F.obj.map I.f.op (J.sheafifiedRepresentableHomEquiv F U alpha) =
        F.obj.map I.f.op (J.sheafifiedRepresentableHomEquiv F U beta) := sorry

/-- The canonical sheafified cover map is an epimorphism. -/
lemma sheafifiedRepresentableCoverMap_epi [HasWeakSheafify J (Type (max u v))]
    (S : J.Cover U) : Epi (sheafifiedRepresentableCoverMap J S) := sorry

/-- The canonical map from the coproduct of sheafified representables of a covering family is
locally surjective. -/
theorem sheafifiedRepresentableCoverMap_isLocallySurjective
    [HasWeakSheafify J (Type (max u v))] :
    Sheaf.IsLocallySurjective (sheafifiedRepresentableCoverMap J S) := sorry

end

end CategoryTheory.GrothendieckTopology
