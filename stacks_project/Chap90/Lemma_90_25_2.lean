module

public import stacks_project.Chap90.Lemma_90_25_2_Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel pair of a morphism of categories cofibered in groupoids

A morphism `f : U ⟶ F` of categories cofibered in groupoids determines a groupoid in
functors `(U, R, s, t, c)` on the base, with `R = U ×_{f, F, f} U`.
-/

@[expose] public section

open CategoryTheory Limits
noncomputable section

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]
variable {U : C ⥤ Type (max v w)}
variable {F : CofiberedCategoryOver.Groupoids.{u, v, max u (max v w), v} C}

/-- Lemma 90.25.2: let `F` be a category cofibered in groupoids over a category `C`, let
`U : C ⥤ Type (max v w)` be a functor, and let `f : Functor.ofTypeValued U ⟶ F` be a morphism of
categories cofibered in groupoids over `C`. Defining `R` as the functor
`U ×_{f, F, f} U`, with `t, s : R ⟶ U` the first and second projections and with
`c : pullback s t ⟶ R` the first-and-last projection of
`U ×_{f, F, f} U ×_{f, F, f} U` under the canonical isomorphism
`pullback s t ≅ U ×_{f, F, f} U ×_{f, F, f} U`, the quintuple `(U, R, s, t, c)` is a
groupoid in functors on `C`. -/
@[stacks 06KY]
noncomputable def ofMorphism (f : Functor.ofTypeValued U ⟶ F) :
    GroupoidInFunctors.{u, v, max v w} C where
  U := U
  R := relation f
  s := src f
  t := tgt f
  c := comp f
  e := identity f
  i := inverse f
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object functor of the kernel-pair groupoid is the given functor `U`. -/
theorem ofMorphism_U (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).U = U := sorry

/-- The arrow functor of the kernel-pair groupoid is `U ×_{f, F, f} U`. -/
theorem ofMorphism_relation (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).R = relation f := sorry

/-- The target map is the first projection of `U ×_{f, F, f} U`. -/
theorem ofMorphism_tgt_eq_fst (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).t = tgt f := sorry

/-- The source map is the second projection of `U ×_{f, F, f} U`. -/
theorem ofMorphism_src_eq_snd (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).s = src f := sorry

/-- Composition is first-and-last projection of the triple product after `composableIso`. -/
theorem ofMorphism_comp_firstLast (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).c = (composableIso f).hom ≫ firstLast f := sorry

end CategoryTheory.GroupoidInFunctors
