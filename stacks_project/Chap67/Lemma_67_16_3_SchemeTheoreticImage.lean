module

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

/-- A morphism vanishes on the kernel of `𝒪_Y ⟶ f_* 𝒪_X`. -/
theorem vanishes_idealSheafSubobject {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : vanishes f (idealSheafSubobject f) :=
  sorry

/-- A `T`-point of `X` composes with `f` to a point of `Y` along which the kernel
ideal of `f` vanishes. -/
theorem vanishes_homOfPoint_idealSheafSubobject {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) {T : (Over S)ᵒᵖ}
    (h : X.functorOfPoints.obj T) :
    vanishes (homOfPoint (f.app T h)) (idealSheafSubobject f) :=
  sorry

/-- For a quasi-compact morphism of algebraic spaces, the kernel of
`𝒪_Y ⟶ f_* 𝒪_X` is a quasi-coherent ideal sheaf on `Y`. -/
instance instIsQuasiCoherent_idealSheafSubobject_of_quasiCompact
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] :
    IsQuasiCoherent (idealSheafSubobject f) :=
  sorry

/-- The factorization of a quasi-compact morphism through the closed subspace cut
out by `Hom.idealSheafSubobject f`. -/
def toIdealImage {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] : X ⟶ subscheme (idealSheafSubobject f) where
  app T := TypeCat.ofHom fun (h : X.functorOfPoints.obj T) ↦
    (⟨f.app T h, vanishes_homOfPoint_idealSheafSubobject f h⟩ :
      (subschemeFunctor (idealSheafSubobject f)).obj T)
  naturality := sorry

/-- On `T`-points, `toIdealImage f` is `f` paired with the kernel-vanishing
witness. -/
theorem toIdealImage_app {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] (T : (Over S)ᵒᵖ)
    (h : X.functorOfPoints.obj T) :
    (toIdealImage f).app T h =
      ⟨f.app T h, vanishes_homOfPoint_idealSheafSubobject f h⟩ :=
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

end Hom

namespace IsSchemeTheoreticImage

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
change along `φ : V ⟶ Y`. -/
theorem of_inverseImage_etale_of_quasiCompact {S : Scheme.{u}}
    {X Y Z V : AlgebraicSpace S} (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι]
    [IsClosedImmersion ι] (φ : V ⟶ Y) [Etale φ] [HasPullback f φ] :
    IsSchemeTheoreticImage (pullback.snd f φ)
      (pullbackToInverseImage f toImage ι φ) (inverseImageι φ ι) :=
  sorry

/-- Scheme-theoretic images of quasi-compact morphisms commute with étale base
change, as a statement about chosen pullbacks. -/
theorem of_pullback_etale_of_quasiCompact {S : Scheme.{u}}
    {X Y Z V : AlgebraicSpace S} (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [QuasiCompact f] [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y)
    [Etale φ] [HasPullback f φ] [HasPullback ι φ] :
    IsSchemeTheoreticImage (pullback.snd f φ)
      (pullbackToImage f toImage ι φ) (pullback.snd ι φ) :=
  sorry

/-- The comparison from a scheme-theoretic image of a quasi-compact morphism to
that image is dominant. Competing factorizations remain explicit, so this is a
theorem on `(f, toImage, ι)` rather than an instance on `toImage` alone. -/
theorem dominant_toImage {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [QuasiCompact f]
    [IsSchemeTheoreticImage f toImage ι] : Dominant toImage :=
  sorry

/-- Factoring through a scheme-theoretic image places `|f|(|X|)` in `|Z|`. -/
theorem range_subset {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    {f : X ⟶ Y} {toImage : X ⟶ Z} {ι : Z ⟶ Y}
    [IsSchemeTheoreticImage f toImage ι] :
    Set.range (Points.map f) ⊆ Set.range (Points.map ι) :=
  sorry

end IsSchemeTheoreticImage

end AlgebraicGeometry.AlgebraicSpace
