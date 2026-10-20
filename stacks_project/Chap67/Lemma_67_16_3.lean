module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.QuasiCompact
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 67.16.3 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact
morphism of algebraic spaces over `S`. Then the sheaf of ideals
`I = Hom.idealSheafSubobject f = Ker(𝒪_Y ⟶ f_* 𝒪_X)` is quasi-coherent. -/
@[stacks 082Z] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.isQuasiCoherent_idealSheafSubobject_of_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f],
      AlgebraicGeometry.AlgebraicSpace.IsQuasiCoherent
        (AlgebraicGeometry.AlgebraicSpace.Hom.idealSheafSubobject f))

/- Lemma 67.16.3 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact
morphism of algebraic spaces over `S` with scheme-theoretic image `Z`. Then `Z`
is the closed subspace corresponding to `I = Hom.idealSheafSubobject f`. -/
@[stacks 082Z] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.idealSheafSubobject_eq :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
      (toImage : X ⟶ Z) (ι : Z ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
      [AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage f toImage ι],
      AlgebraicGeometry.AlgebraicSpace.Hom.idealSheafSubobject ι =
        AlgebraicGeometry.AlgebraicSpace.Hom.idealSheafSubobject f)

/- Lemma 67.16.3 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact
morphism of algebraic spaces over `S` with scheme-theoretic image `Z`. For any
étale morphism `φ : V ⟶ Y`, the scheme-theoretic image of `X ×_Y V ⟶ V` is
`Z ×_Y V`, as the closed inverse image of `ι` along `φ`. -/
@[stacks 082Z] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.instOfInverseImageEtale_of_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S} (f : X ⟶ Y)
      (toImage : X ⟶ Z) (ι : Z ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
      [AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage f toImage ι]
      [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion ι] (φ : V ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.Etale φ] [HasPullback f φ],
      AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage (pullback.snd f φ)
        (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.pullbackToInverseImage
          f toImage ι φ)
        (AlgebraicGeometry.AlgebraicSpace.inverseImageι φ ι))

/- Lemma 67.16.3 (4): Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact
morphism of algebraic spaces over `S` with scheme-theoretic image `Z`. Then
`|f|(|X|) ⊂ |Z|` is dense in `|Z|`. -/
@[stacks 082Z] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage.dominant_toImage :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
      (toImage : X ⟶ Z) (ι : Z ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
      [AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage f toImage ι],
      AlgebraicGeometry.AlgebraicSpace.Dominant toImage)
