/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom
public import ReasLib.CategoryTheory.Sites.Cover.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
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
        (Limits.Sigma.desc (fun i : ι => CategoryTheory.uliftYoneda.{max u v}.map (f i))) := by
  let L := presheafToSheaf J (Type (max u v))
  let X := fun i ↦ uliftYoneda.{max u v}.obj (Y i)
  let q := Sigma.desc fun i ↦ uliftYoneda.{max u v}.map (f i)
  have fac : sigmaComparison L X ≫ L.map q =
      Sigma.desc (fun i ↦ J.sheafifiedRepresentableMap (f i)) := by
    change sigmaComparison L X ≫ L.map q =
      Sigma.desc (fun i ↦ L.map (uliftYoneda.{max u v}.map (f i)))
    dsimp only [q]
    rw [sigmaComparison_map_desc]
  change Presheaf.IsLocallySurjective J
    (Sigma.desc fun i ↦ J.sheafifiedRepresentableMap (f i)).hom ↔ _
  rw [← fac]
  change Presheaf.IsLocallySurjective J
    ((sigmaComparison L X).hom ≫ (L.map q).hom) ↔ _
  rw [Presheaf.comp_isLocallySurjective_iff]
  exact Presheaf.isLocallySurjective_presheafToSheaf_map_iff J q

variable {J}
variable {U : C} (S : J.Cover U)

/-- Sections of a sheaf over a covered object are determined by their restrictions to the cover. -/
lemma section_eq_of_cover_restrictions_eq
    {F : Sheaf J (Type (max u v))} {s t : F.obj.obj (op U)}
    (h : forall I : S.Arrow, F.obj.map I.f.op s = F.obj.map I.f.op t) :
    s = t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 F.property) _ S.property).isSeparatedFor.ext
  intro V f hf
  exact h ⟨V, f, hf⟩

/-- Equality after precomposition with a canonical cover map gives equality on every cover
component. -/
lemma cover_component_eq_of_coverMap_comp_eq
    [HasWeakSheafify J (Type (max u v))]
    {F : Sheaf J (Type (max u v))} {alpha beta : J.sheafifiedRepresentable U ⟶ F}
    (h : sheafifiedRepresentableCoverMap J S ≫ alpha =
      sheafifiedRepresentableCoverMap J S ≫ beta) :
    forall I : S.Arrow,
      F.obj.map I.f.op (J.sheafifiedRepresentableHomEquiv F U alpha) =
        F.obj.map I.f.op (J.sheafifiedRepresentableHomEquiv F U beta) := by
  intro I
  have hc : J.sheafifiedRepresentableMap I.f ≫ alpha =
      J.sheafifiedRepresentableMap I.f ≫ beta := by
    simpa only [sheafifiedRepresentableCoverMap, Sigma.ι_desc_assoc] using
      congrArg (fun k ↦ Sigma.ι (fun I : S.Arrow ↦ J.sheafifiedRepresentable I.Y) I ≫ k) h
  change F.obj.map I.f.op
      (uliftYonedaEquiv ((sheafificationAdjunction J (Type (max u v))).homEquiv _ F alpha)) =
    F.obj.map I.f.op
      (uliftYonedaEquiv ((sheafificationAdjunction J (Type (max u v))).homEquiv _ F beta))
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
  congr 1
  exact ((sheafificationAdjunction J (Type (max u v))).homEquiv_naturality_left
      (uliftYoneda.map I.f) alpha).symm.trans
    ((congrArg ((sheafificationAdjunction J (Type (max u v))).homEquiv _ F) hc).trans
      ((sheafificationAdjunction J (Type (max u v))).homEquiv_naturality_left
        (uliftYoneda.map I.f) beta))

/-- The canonical sheafified cover map is an epimorphism. -/
lemma sheafifiedRepresentableCoverMap_epi [HasWeakSheafify J (Type (max u v))]
    (S : J.Cover U) : Epi (sheafifiedRepresentableCoverMap J S) := by
  apply (Sheaf.isLocallySurjective_iff_epi _).1
  apply (isLocallySurjective_sigmaDesc_sheafifiedRepresentableMap_iff J
    (fun I : S.Arrow ↦ I.Y) (fun I ↦ I.f)).2
  apply (J.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
    (fun I : S.Arrow ↦ I.f)).1
  apply J.superset_covering ?_ S.property
  intro V f hf
  exact Sieve.ofArrows_mk (Y := fun I : S.Arrow ↦ I.Y)
    (f := fun I : S.Arrow ↦ I.f) (⟨V, f, hf⟩ : S.Arrow)

/-- The canonical map from the coproduct of sheafified representables of a covering family is
locally surjective. -/
theorem sheafifiedRepresentableCoverMap_isLocallySurjective
    [HasWeakSheafify J (Type (max u v))] :
    Sheaf.IsLocallySurjective (sheafifiedRepresentableCoverMap J S) := by
  letI := sheafifiedRepresentableCoverMap_epi S
  exact (Sheaf.isLocallySurjective_iff_epi _).2 inferInstance

end

end CategoryTheory.GrothendieckTopology
