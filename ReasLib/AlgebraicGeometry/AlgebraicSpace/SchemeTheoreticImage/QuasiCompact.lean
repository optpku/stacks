/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Quasi-compact scheme-theoretic images

The kernel ideal of a quasi-compact morphism of algebraic spaces is quasi-coherent.
Its closed subspace is the scheme-theoretic image, formation of the image commutes
with étale base change, and the source maps densely into the image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A morphism vanishes on the kernel of `𝒪_Y ⟶ f_* 𝒪_X`. -/
theorem vanishes_idealSheafSubobject {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : vanishes f (idealSheafSubobject f) :=
  sorry

/-- A `T`-point of `X` composes with `f` to a point of `Y` along which the kernel
ideal of `f` vanishes. -/
private theorem vanishes_homOfPoint_idealSheafSubobject {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) {T : (Over S)ᵒᵖ}
    (h : X.functorOfPoints.obj T) :
    vanishes (homOfPoint (f.app T h)) (idealSheafSubobject f) :=
  sorry

/-- The kernel of the structure-sheaf map of a quasi-compact morphism of algebraic
spaces is a quasi-coherent ideal sheaf on its target. -/
instance isQuasiCoherent_idealSheafSubobject_of_quasiCompact
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] :
    IsQuasiCoherent (idealSheafSubobject f) :=
  sorry

/-- The pointwise factorization through the vanishing functor of the kernel ideal
commutes with restriction along morphisms of test schemes. -/
private theorem toIdealImage_naturality {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') :
    X.functorOfPoints.map φ ≫
        TypeCat.ofHom (fun (h : X.functorOfPoints.obj T') ↦
          (⟨f.app T' h, vanishes_homOfPoint_idealSheafSubobject f h⟩ :
            (subschemeFunctor (idealSheafSubobject f)).obj T')) =
      TypeCat.ofHom (fun (h : X.functorOfPoints.obj T) ↦
        (⟨f.app T h, vanishes_homOfPoint_idealSheafSubobject f h⟩ :
          (subschemeFunctor (idealSheafSubobject f)).obj T)) ≫
        (subschemeFunctor (idealSheafSubobject f)).map φ :=
  sorry

/-- The scheme-theoretic image of a quasi-compact morphism is the closed
subspace cut out by the kernel of its structure-sheaf map. -/
noncomputable def schemeTheoreticImage
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] :
    ClosedSubspace Y :=
  @ClosedSubspace.ofQuasiCoherentIdeal S Y (idealSheafSubobject f)
    (isQuasiCoherent_idealSheafSubobject_of_quasiCompact f)

/-- The scheme-theoretic image inclusion is the canonical inclusion of the
closed subspace cut out by the kernel ideal. -/
theorem schemeTheoreticImage_ι
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] :
    (schemeTheoreticImage f).ι =
      subschemeFunctorι (idealSheafSubobject f) :=
  @ClosedSubspace.ofQuasiCoherentIdeal_ι S Y (idealSheafSubobject f)
    (isQuasiCoherent_idealSheafSubobject_of_quasiCompact f)

/-- The ideal sheaf of the scheme-theoretic image is the kernel of the
structure-sheaf map of the original morphism. -/
theorem schemeTheoreticImage_idealSheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] :
    (schemeTheoreticImage f).idealSheaf = idealSheafSubobject f :=
  @ClosedSubspace.ofQuasiCoherentIdeal_idealSheaf S Y (idealSheafSubobject f)
    (isQuasiCoherent_idealSheafSubobject_of_quasiCompact f)

/-- The factorization of a quasi-compact morphism through the closed subspace cut
out by `Hom.idealSheafSubobject f`. -/
def toIdealImage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] : X ⟶ subscheme (idealSheafSubobject f) where
  app T := TypeCat.ofHom fun (h : X.functorOfPoints.obj T) ↦
    (⟨f.app T h, by exact vanishes_homOfPoint_idealSheafSubobject f h⟩ :
      (subschemeFunctor (idealSheafSubobject f)).obj T)
  naturality := by
    intro T T' φ
    exact toIdealImage_naturality f φ

/-- The underlying `T`-point of `toIdealImage f` is the image under `f`. -/
theorem toIdealImage_app {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] (T : (Over S)ᵒᵖ)
    (h : X.functorOfPoints.obj T) :
    ((toIdealImage f).app T h).val = f.app T h :=
  sorry

/-- `toIdealImage f` composed with the closed-subspace inclusion is `f`. -/
theorem toIdealImage_comp_subschemeι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] :
    toIdealImage f ≫ subschemeι (idealSheafSubobject f) = f :=
  sorry

/-- The kernel-subscheme factorization of a quasi-compact morphism is a
scheme-theoretic image factorization. -/
instance instIsSchemeTheoreticImage_toIdealImage {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticImage f (toIdealImage f)
      (subschemeι (idealSheafSubobject f)) :=
  sorry

/-- The canonical map from the source to the kernel subscheme of a quasi-compact
morphism is dominant. -/
instance instDominant_toIdealImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] : Dominant (toIdealImage f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom

namespace AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage

/-- A scheme-theoretic image of a quasi-compact morphism has the same kernel
ideal sheaf as the original morphism. -/
theorem idealSheafSubobject_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [QuasiCompact f]
    [IsSchemeTheoreticImage f toImage ι] :
    Hom.idealSheafSubobject ι = Hom.idealSheafSubobject f :=
  sorry

/-- Any scheme-theoretic image of a quasi-compact morphism admits a unique
comparison over `Y` to the kernel subscheme. -/
theorem existsUnique_toIdealImage {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [QuasiCompact f]
    [IsSchemeTheoreticImage f toImage ι] :
    ∃! k : Z ⟶ subscheme (Hom.idealSheafSubobject f),
      k ≫ subschemeι (Hom.idealSheafSubobject f) = ι ∧
        toImage ≫ k = Hom.toIdealImage f :=
  sorry

/-- Scheme-theoretic images of quasi-compact morphisms commute with étale base
change, as a statement about the closed inverse image. -/
instance instOfInverseImageEtale_of_quasiCompact {S : Scheme.{u}}
    {X Y Z V : AlgebraicSpace S} (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι]
    [IsClosedImmersion ι] (φ : V ⟶ Y) [Etale φ] [HasPullback f φ] :
    IsSchemeTheoreticImage (pullback.snd f φ)
      (pullbackToInverseImage f toImage ι φ) (inverseImageι φ ι) :=
  sorry

/-- Scheme-theoretic images of quasi-compact morphisms commute with étale base
change, as a statement about chosen pullbacks. -/
instance of_pullback_etale_of_quasiCompact {S : Scheme.{u}}
    {X Y Z V : AlgebraicSpace S} (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y)
    [Etale φ] [HasPullback f φ] [HasPullback ι φ] :
    IsSchemeTheoreticImage (pullback.snd f φ)
      (pullbackToImage f toImage ι φ) (pullback.snd ι φ) :=
  sorry

/-- The factorization map from the source of a quasi-compact morphism to its
scheme-theoretic image is dominant. -/
theorem dominant_toImage {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [QuasiCompact f]
    [IsSchemeTheoreticImage f toImage ι] : Dominant toImage :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage
