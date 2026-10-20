module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.Flat
import StacksCheckRecall

/-!
# Flat base change of scheme-theoretic images

Scheme-theoretic images of quasi-compact morphisms of algebraic spaces commute
with inverse image along a flat morphism.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsSchemeTheoreticImage

/- Lemma 67.30.12: Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
algebraic spaces over `S`. Let `g : V ⟶ Y` be a quasi-compact morphism of
algebraic spaces. If `ι : Z ⟶ Y` is a scheme-theoretic image of `g`, then
`inverseImageι f ι` is a scheme-theoretic image of `pullback.snd g f`. In
particular the scheme-theoretic image of `V ×_Y X ⟶ X` equals `f⁻¹Z`. -/
@[stacks 089E] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.instOfInverseImageFlat_of_quasiCompact :
  ∀ {S : Scheme.{u}}
    {X Y V Z : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] (g : V ⟶ Y)
    [QuasiCompact g] (toImage : V ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage g toImage ι] [IsClosedImmersion ι]
    [HasPullback g f],
    IsSchemeTheoreticImage (pullback.snd g f)
      (pullbackToInverseImage g toImage ι f) (inverseImageι f ι))

/- Scheme-theoretic images of quasi-compact morphisms commute with pullback along
a flat morphism, as a statement about chosen pullbacks. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.of_pullback_flat_of_quasiCompact :
  ∀ {S : Scheme.{u}}
    {X Y V Z : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] (g : V ⟶ Y)
    [QuasiCompact g] (toImage : V ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage g toImage ι] [HasPullback g f] [HasPullback ι f],
    IsSchemeTheoreticImage (pullback.snd g f)
      (pullbackToImage g toImage ι f) (pullback.snd ι f))

end IsSchemeTheoreticImage

namespace Hom

/- The kernel of `pullback.snd g f` equals the kernel of the closed inverse image
of the kernel-subscheme of a quasi-compact morphism `g` along a flat morphism
`f`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.idealSheafSubobject_pullback_snd_of_flat :
  ∀ {S : Scheme.{u}}
    {X Y V : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] (g : V ⟶ Y)
    [QuasiCompact g] [HasPullback g f],
    idealSheafSubobject (pullback.snd g f) =
      idealSheafSubobject (inverseImageι f (subschemeι (idealSheafSubobject g))))

end Hom

end AlgebraicGeometry.AlgebraicSpace
