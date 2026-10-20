/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc.Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u v w

/- Lemma 74.7.2: if `{T_i ⟶ T}` is an fpqc covering of algebraic spaces over a
scheme `S`, then for every algebraic space `B` over `S` the diagram
`Mor_S(T, B) → ∏ i, Mor_S(T_i, B) ⇉ ∏ i j, Mor_S(T_i ×_T T_j, B)` is an
equalizer. In particular, `yoneda.obj B` satisfies the sheaf condition for the
covering presieve. -/
@[stacks 04P2] #check
  (AlgebraicGeometry.AlgebraicSpace.FpqcCovering.isSheafFor_yoneda :
    ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
      {family : ι → Over T} (hfamily : FpqcCovering family)
      (B : AlgebraicSpace S),
      Presieve.IsSheafFor (yoneda.obj B)
        (Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)))

#check (AlgebraicGeometry.AlgebraicSpace.FpqcCovering.existsUnique_hom :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family)
    {B : AlgebraicSpace S} (g : (i : ι) → (family i).left ⟶ B)
    (hcompat : ∀ i j,
      pullback.fst (family i).hom (family j).hom ≫ g i =
        pullback.snd (family i).hom (family j).hom ≫ g j),
    ∃! f : T ⟶ B, ∀ i, (family i).hom ≫ f = g i)

#check (AlgebraicGeometry.AlgebraicSpace.FpqcCovering.isSheafFor_of_isRepresentable :
  ∀ {S : Scheme.{u}} {P : (AlgebraicSpace S)ᵒᵖ ⥤ Type w} [P.IsRepresentable]
    {T : AlgebraicSpace S} {ι : Type v} {family : ι → Over T}
    (hfamily : FpqcCovering family),
    Presieve.IsSheafFor P
      (Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)))

#check (AlgebraicGeometry.AlgebraicSpace.FpqcCovering.effectiveEpimorphic :
  ∀ {S : Scheme.{u}} {T : AlgebraicSpace S} {ι : Type v}
    {family : ι → Over T} (hfamily : FpqcCovering family),
    (Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)).EffectiveEpimorphic)
