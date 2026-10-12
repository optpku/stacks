/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_16_3_SchemeTheoreticImage
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Flat base change of scheme-theoretic images

Scheme-theoretic images of quasi-compact morphisms of algebraic spaces commute
with inverse image along a flat morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsSchemeTheoreticImage

/-- Lemma 67.30.12: Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
algebraic spaces over `S`. Let `g : V ⟶ Y` be a quasi-compact morphism of
algebraic spaces. If `ι : Z ⟶ Y` is a scheme-theoretic image of `g`, then
`inverseImageι f ι` is a scheme-theoretic image of `pullback.snd g f`. In
particular the scheme-theoretic image of `V ×_Y X ⟶ X` equals `f⁻¹Z`. -/
@[stacks 089E]
instance instOfInverseImageFlat_of_quasiCompact {S : Scheme.{u}}
    {X Y V Z : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] (g : V ⟶ Y)
    [QuasiCompact g] (toImage : V ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage g toImage ι] [IsClosedImmersion ι]
    [HasPullback g f] :
    IsSchemeTheoreticImage (pullback.snd g f)
      (pullbackToInverseImage g toImage ι f) (inverseImageι f ι) :=
  sorry

/-- Scheme-theoretic images of quasi-compact morphisms commute with pullback along
a flat morphism, as a statement about chosen pullbacks. -/
theorem of_pullback_flat_of_quasiCompact {S : Scheme.{u}}
    {X Y V Z : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] (g : V ⟶ Y)
    [QuasiCompact g] (toImage : V ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage g toImage ι] [HasPullback g f] [HasPullback ι f] :
    IsSchemeTheoreticImage (pullback.snd g f)
      (pullbackToImage g toImage ι f) (pullback.snd ι f) :=
  sorry

end IsSchemeTheoreticImage

namespace Hom

/-- The kernel of `pullback.snd g f` equals the kernel of the closed inverse image
of the kernel-subscheme of a quasi-compact morphism `g` along a flat morphism
`f`. -/
theorem idealSheafSubobject_pullback_snd_of_flat {S : Scheme.{u}}
    {X Y V : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] (g : V ⟶ Y)
    [QuasiCompact g] [HasPullback g f] :
    idealSheafSubobject (pullback.snd g f) =
      idealSheafSubobject (inverseImageι f (subschemeι (idealSheafSubobject g))) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
