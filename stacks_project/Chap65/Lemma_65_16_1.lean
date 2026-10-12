/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase

/-!
# Lemma 65.16.1

Change of base scheme for sheaves, representables, and algebraic spaces along a
morphism `g : S ⟶ S'` in the big fppf site, with localization functor
`j = Over.map g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 65.16.1 (1): let `g : S ⟶ S'` be a morphism of schemes and write
`j = Over.map g` for the localization functor `(Sch/S)_fppf ⟶ (Sch/S')_fppf`. For a sheaf of
sets `F` on `(Sch/S)_fppf` and a scheme `T'` over `S'`, the value `j_! F (T'/S')` is the
coproduct of `F(T' ⟶ S)` over morphisms `φ : T' ⟶ Over.mk g`. -/
@[stacks 03I4]
theorem extendBasePresheaf_obj {S S' : Scheme.{u}} (g : S ⟶ S')
    (F : (Over S)ᵒᵖ ⥤ Type u) (T' : Over S') :
    (extendBasePresheaf g F).obj (op T') =
      Σ φ : T' ⟶ Over.mk g, F.obj (op (Over.mk φ.left)) := sorry

/-- Lemma 65.16.1 (2): if `F` is representable by a scheme `X` over `S`, then `j_! F` is
representable by `j(X)`, which is `X` viewed as a scheme over `S'` via `Over.map g`. -/
@[stacks 03I4]
def extendBase_ofOver {S S' : Scheme.{u}} (g : S ⟶ S') (X : Over S) :
    extendBasePresheaf g (yoneda.obj X) ≅ yoneda.obj ((Over.map g).obj X) :=
  extendBasePresheafYonedaIso g X

/-- The identification of Lemma 65.16.1 (2) is the coproduct-to-yoneda comparison. -/
theorem extendBase_ofOver_eq {S S' : Scheme.{u}} (g : S ⟶ S') (X : Over S) :
    extendBase_ofOver g X = extendBasePresheafYonedaIso g X := sorry

/-- Lemma 65.16.1 (3): if `F` is an algebraic space over `S`, then `j_! F` is an algebraic
space over `S'`. If `F = U/R` is a presentation, then `j_! F = j(U)/j(R)` is a presentation,
via `Presentation.extendBase`. -/
@[stacks 03I4]
theorem extendBase_spec {S S' : Scheme.{u}} (g : S ⟶ S') (F : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S') (extendBase g F).functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag (extendBase g F).functorOfPoints) ∧
        ∃ (U : Over S') (p : yoneda.obj U ⟶ (extendBase g F).functorOfPoints),
          (MorphismProperty.over (@Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S') p := sorry

/-- Lemma 65.16.1 (4): for a sheaf of sets `F'` on `(Sch/S')_fppf` and a scheme `T` over `S`,
the inverse image satisfies `j⁻¹ F' (T/S) = F' (T/S')`, i.e. evaluation after applying
`j = Over.map g`. -/
@[stacks 03I4]
theorem baseChangePresheaf_obj {S S' : Scheme.{u}} (g : S ⟶ S')
    (F' : (Over S')ᵒᵖ ⥤ Type u) (T : Over S) :
    (baseChangePresheaf g F').obj (op T) = F'.obj (op ((Over.map g).obj T)) := sorry

/-- Lemma 65.16.1 (5): if `F'` is representable by a scheme `X'` over `S'`, then `j⁻¹ F'` is
representable by `X'_S = S ×_{S'} X'`, the chosen object `(Over.pullback g).obj X'`. -/
@[stacks 03I4]
def baseChange_ofOver {S S' : Scheme.{u}} (g : S ⟶ S') (X' : Over S') :
    baseChangePresheaf g (yoneda.obj X') ≅ yoneda.obj ((Over.pullback g).obj X') :=
  baseChangePresheafYonedaIso g X'

/-- The identification of Lemma 65.16.1 (5) is the adjunction comparison for `Over.map g`. -/
theorem baseChange_ofOver_eq {S S' : Scheme.{u}} (g : S ⟶ S') (X' : Over S') :
    baseChange_ofOver g X' = baseChangePresheafYonedaIso g X' := sorry

/-- Lemma 65.16.1 (6): if `F'` is an algebraic space over `S'`, then `j⁻¹ F'` is an algebraic
space over `S`. If `F' = U'/R'` is a presentation, then `j⁻¹ F' = U'_S / R'_S` is a
presentation, via `Presentation.baseChange`. -/
@[stacks 03I4]
theorem baseChange_spec {S S' : Scheme.{u}} (g : S ⟶ S') (F' : AlgebraicSpace S') :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (baseChange g F').functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag (baseChange g F').functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ (baseChange g F').functorOfPoints),
          (MorphismProperty.over (@Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

end AlgebraicGeometry.AlgebraicSpace
