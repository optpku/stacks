/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- A monomorphism of finite étale covers is a monomorphism of schemes. -/
theorem mono_left {X : Scheme.{u}} {Y Z : FiniteEtale X}
    (i : Y ⟶ Z) [Mono i] : Mono i.left := sorry

/-- A monomorphism of finite étale covers identifies an open subscheme.
The section inverses come from the native flat-monomorphism construction. -/
instance mono_isOpenImmersion {X : Scheme.{u}} {Y Z : FiniteEtale X}
    (i : Y ⟶ Z) [Mono i] : IsOpenImmersion i.left := by
  letI : Mono i.left := mono_left i
  letI : Etale i.left :=
    MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale)
      i.left Z.hom Z.prop.2 (by rw [MorphismProperty.Over.w i]; exact Y.prop.2)
  exact IsOpenImmersion.of_flat_of_mono i.left

variable {X : Scheme.{u}} {Y Z : FiniteEtale X} (i : Y ⟶ Z) [mono : Mono i]

include mono

/-- The image of a monomorphism of finite étale covers is closed as well as open. -/
theorem mono_isClosed_range : IsClosed (Set.range i.left) := sorry

/-- The open complement of the image of a finite étale monomorphism. -/
def monoComplementOpen : Z.left.Opens :=
  ⟨(Set.range i.left)ᶜ, (mono_isClosed_range i).isOpen_compl⟩

/-- The structural morphism of the complementary open subscheme is finite étale. -/
theorem monoComplementOpen_finiteEtale :
    finiteEtaleMorphism ((monoComplementOpen i).ι ≫ Z.hom) := sorry

/-- The actual complementary finite étale cover. -/
def monoComplement : FiniteEtale X where
  toComma := Over.mk ((monoComplementOpen i).ι ≫ Z.hom)
  prop := monoComplementOpen_finiteEtale i

/-- The inclusion of the complementary cover. -/
def monoComplementInclusion : monoComplement i ⟶ Z :=
  MorphismProperty.Over.homMk (monoComplementOpen i).ι (by rfl)

/-- The original cover and its complement form the two pieces of an open cover. -/
def monoComplementCover : Z.left.OpenCover where
  I₀ := Bool
  X b := if b then Y.left else (monoComplementOpen i).toScheme
  f b := by
    cases b
    · exact (monoComplementOpen i).ι
    · exact i.left
  mem₀ := sorry

/-- The morphism on each of the two pieces of the complementary open cover. -/
def monoComplementCoverMap {T : FiniteEtale X}
    (f : Y ⟶ T) (g : monoComplement i ⟶ T) (b : Bool) :
    (monoComplementCover i).X b ⟶ T.left := by
  cases b
  · exact g.left
  · exact f.left

/-- Maps on the two disjoint pieces agree on their overlaps. -/
theorem monoComplementCover_compatible {T : FiniteEtale X}
    (f : Y ⟶ T) (g : monoComplement i ⟶ T) :
    ∀ a b,
      pullback.fst ((monoComplementCover i).f a) ((monoComplementCover i).f b) ≫
          monoComplementCoverMap i f g a =
        pullback.snd ((monoComplementCover i).f a) ((monoComplementCover i).f b) ≫
          monoComplementCoverMap i f g b := sorry

/-- Glue two maps out of the clopen summands using the native scheme open-cover descent. -/
noncomputable def monoComplementDescLeft {T : FiniteEtale X}
    (f : Y ⟶ T) (g : monoComplement i ⟶ T) : Z.left ⟶ T.left :=
  (monoComplementCover i).glueMorphisms
    (monoComplementCoverMap i f g)
    (monoComplementCover_compatible i f g)

/-- The glued morphism lies over the base. -/
theorem monoComplementDescLeft_over {T : FiniteEtale X}
    (f : Y ⟶ T) (g : monoComplement i ⟶ T) :
    monoComplementDescLeft i f g ≫ T.hom = Z.hom := sorry

/-- The coproduct descent morphism has the actual scheme-gluing map as its underlying map. -/
noncomputable def monoComplementDesc {T : FiniteEtale X}
    (f : Y ⟶ T) (g : monoComplement i ⟶ T) : Z ⟶ T :=
  MorphismProperty.Over.homMk (monoComplementDescLeft i f g)
    (monoComplementDescLeft_over i f g)

/-- A finite étale monomorphism and its concrete clopen complement exhibit a binary coproduct. -/
noncomputable def monoComplementIsColimit :
    IsColimit (BinaryCofan.mk i (monoComplementInclusion i)) :=
  BinaryCofan.IsColimit.mk _ (monoComplementDesc i)
    (by intro T f g; sorry)
    (by intro T f g; sorry)
    (by intro T f g m hf hg; sorry)

/-- Every finite étale monomorphism is the inclusion of a direct summand. -/
theorem monoInducesIsoOnDirectSummand :
    ∃ (W : FiniteEtale X) (j : W ⟶ Z), Nonempty (IsColimit (BinaryCofan.mk i j)) :=
  ⟨monoComplement i, monoComplementInclusion i, ⟨monoComplementIsColimit i⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale
