/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

namespace FpqcCovering

/-- Lemma 74.7.2: if `{T_i ⟶ T}` is an fpqc covering of algebraic spaces over a
scheme `S`, then for every algebraic space `B` over `S` the diagram
`Mor_S(T, B) → ∏ i, Mor_S(T_i, B) ⇉ ∏ i j, Mor_S(T_i ×_T T_j, B)` is an
equalizer. In particular, `yoneda.obj B` satisfies the sheaf condition for the
covering presieve. -/
@[stacks 04P2]
theorem isSheafFor_yoneda {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family)
    (B : AlgebraicSpace S) :
    Presieve.IsSheafFor (yoneda.obj B)
      (Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) :=
  sorry

/-- Compatible morphisms `T_i ⟶ B` on an fpqc covering family glue uniquely to a
morphism `T ⟶ B`. -/
theorem existsUnique_hom {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family)
    {B : AlgebraicSpace S} (g : (i : ι) → (family i).left ⟶ B)
    (hcompat : ∀ i j,
      pullback.fst (family i).hom (family j).hom ≫ g i =
        pullback.snd (family i).hom (family j).hom ≫ g j) :
    ∃! f : T ⟶ B, ∀ i, (family i).hom ≫ f = g i :=
  sorry

/-- Every representable functor on algebraic spaces over `S` satisfies the sheaf
condition for an fpqc covering family. -/
theorem isSheafFor_of_isRepresentable {S : Scheme.{u}}
    {P : (AlgebraicSpace S)ᵒᵖ ⥤ Type (u + 1)} [P.IsRepresentable]
    {T : AlgebraicSpace S} {ι : Type v} {family : ι → Over T}
    (hfamily : FpqcCovering family) :
    Presieve.IsSheafFor P
      (Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) :=
  sorry

/-- An fpqc covering family of algebraic spaces is effective epimorphic. -/
theorem isEffectiveEpiFamily {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family) :
    EffectiveEpiFamily (fun i ↦ (family i).left) (fun i ↦ (family i).hom) :=
  sorry

end FpqcCovering

end AlgebraicGeometry.AlgebraicSpace
