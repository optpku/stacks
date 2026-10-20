/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.QuasiCompact
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Lemma_67_16_4_SchemeTheoreticImage
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf

/-!
# Quasi-compact scheme-theoretic images

If `f : X ⟶ Y` is quasi-compact, the kernel ideal `Hom.idealSheafSubobject f`
is quasi-coherent, `f` factors through the closed subspace it cuts out, this
factorization is a scheme-theoretic image, and the image is stable under étale
base change and dominant onto its closed subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.vanishes_idealSheafSubobject :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
      vanishes f (idealSheafSubobject f))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.isQuasiCoherent_idealSheafSubobject_of_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f],
      IsQuasiCoherent (idealSheafSubobject f))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toIdealImage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f],
      X ⟶ subscheme (idealSheafSubobject f))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toIdealImage_app :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] (T : (Over S)ᵒᵖ)
    (h : X.functorOfPoints.obj T),
      ((toIdealImage f).app T h).val = f.app T h)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.toIdealImage_comp_subschemeι :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f],
      toIdealImage f ≫ subschemeι (idealSheafSubobject f) = f)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.instIsSchemeTheoreticImage_toIdealImage :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f],
      IsSchemeTheoreticImage f (toIdealImage f)
      (subschemeι (idealSheafSubobject f)))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.instDominant_toIdealImage :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f],
      Dominant (toIdealImage f))

end Hom

namespace IsSchemeTheoreticImage

#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.idealSheafSubobject_eq :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [QuasiCompact f]
    [IsSchemeTheoreticImage f toImage ι],
      Hom.idealSheafSubobject ι = Hom.idealSheafSubobject f)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.existsUnique_toIdealImage :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [QuasiCompact f]
    [IsSchemeTheoreticImage f toImage ι],
      ∃! k : Z ⟶ subscheme (Hom.idealSheafSubobject f),
      k ≫ subschemeι (Hom.idealSheafSubobject f) = ι ∧
        toImage ≫ k = Hom.toIdealImage f)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.instOfInverseImageEtale_of_quasiCompact :
    ∀ {S : Scheme.{u}}
    {X Y Z V : AlgebraicSpace S} (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι]
    [IsClosedImmersion ι] (φ : V ⟶ Y) [Etale φ] [HasPullback f φ],
      IsSchemeTheoreticImage (pullback.snd f φ)
      (pullbackToInverseImage f toImage ι φ) (inverseImageι φ ι))

#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.of_pullback_etale_of_quasiCompact :
    ∀ {S : Scheme.{u}}
    {X Y Z V : AlgebraicSpace S} (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y)
    [Etale φ] [HasPullback f φ] [HasPullback ι φ],
      IsSchemeTheoreticImage (pullback.snd f φ)
      (pullbackToImage f toImage ι φ) (pullback.snd ι φ))

#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.dominant_toImage :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [QuasiCompact f]
    [IsSchemeTheoreticImage f toImage ι],
      Dominant toImage)

end IsSchemeTheoreticImage

end AlgebraicGeometry.AlgebraicSpace
