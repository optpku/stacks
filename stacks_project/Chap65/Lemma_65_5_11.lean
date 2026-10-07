module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/-- Lemma 65.5.11: let `S` be a scheme and let `F` be a presheaf of sets
`(Over S)ᵒᵖ ⥤ Type u` on `(Sch/S)_fppf`. Let `P` be a property of morphisms of
schemes in the sense of Definition 65.5.1 that is stable under base change.
If for every `U`, `V` in `Over S` and Yoneda sections `ξ : yoneda.obj U ⟶ F`,
`ξ' : yoneda.obj V ⟶ F` the pairwise fibre product `pullback ξ ξ'` is
representable and the comparison
`prod.lift (pullback.fst ξ ξ') (pullback.snd ξ ξ') :
  pullback ξ ξ' ⟶ yoneda.obj U ⨯ yoneda.obj V`
(that is, `h_U ×_{ξ, F, ξ'} h_V ⟶ h_U × h_V`) has property `(over P).presheaf`,
then the diagonal `diag F : F ⟶ F ⨯ F` has property `(over P).presheaf`.
By Lemma 65.5.3, that comparison has `(over P).presheaf` if and only if the
corresponding scheme morphism `W ⟶ U ×_S V` has property `P`. -/
@[stacks 0CB7]
lemma over_presheaf_diag {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {F : (Over S)ᵒᵖ ⥤ Type u}
    (h_rep : ∀ (U V : Over S) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
      (pullback ξ ξ').IsRepresentable)
    (hP : ∀ (U V : Over S) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
      (over P).presheaf (prod.lift (pullback.fst ξ ξ') (pullback.snd ξ ξ'))) :
    (over P).presheaf (diag F) := sorry

/-- The diagonal `diag F` has property `(over P).presheaf` if and only if every
pairwise fibre product of Yoneda sections is representable and the comparison
`prod.lift (pullback.fst ξ ξ') (pullback.snd ξ ξ')` has property
`(over P).presheaf`. -/
lemma over_presheaf_diag_iff {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {F : (Over S)ᵒᵖ ⥤ Type u} :
    (over P).presheaf (diag F) ↔
      ∀ (U V : Over S) (ξ : yoneda.obj U ⟶ F) (ξ' : yoneda.obj V ⟶ F),
        (pullback ξ ξ').IsRepresentable ∧
          (over P).presheaf (prod.lift (pullback.fst ξ ξ') (pullback.snd ξ ξ')) := sorry
