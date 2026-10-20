/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

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

/-- Scheme-theoretic images of quasi-compact morphisms of algebraic spaces
commute with flat base change, as a statement about the closed inverse image. -/
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
instance of_pullback_flat_of_quasiCompact {S : Scheme.{u}}
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
