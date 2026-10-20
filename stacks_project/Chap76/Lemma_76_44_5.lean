module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 76.44.5 (1): Let `S` be a scheme. Let `i : Z ⟶ X` be a Koszul-regular
immersion of algebraic spaces over `S`. Let `f : X' ⟶ X` be a flat morphism of
algebraic spaces over `S`. Then `pullback.snd i f : Z ×[X] X' ⟶ X'` is a
Koszul-regular immersion. -/
@[stacks 09RX] #check
  (AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion.pullback_snd :
    ∀ {S : Scheme.{u}} {Z X X' : AlgebraicSpace S} (i : Z ⟶ X) (f : X' ⟶ X)
      [HasPullback i f] [IsKoszulRegularImmersion i] [Flat f],
      IsKoszulRegularImmersion (pullback.snd i f))

/- Lemma 76.44.5 (2): Let `S` be a scheme. Let `i : Z ⟶ X` be an `H₁`-regular
immersion of algebraic spaces over `S`. Let `f : X' ⟶ X` be a flat morphism of
algebraic spaces over `S`. Then `pullback.snd i f : Z ×[X] X' ⟶ X'` is an
`H₁`-regular immersion. -/
@[stacks 09RX] #check
  (AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion.pullback_snd :
    ∀ {S : Scheme.{u}} {Z X X' : AlgebraicSpace S} (i : Z ⟶ X) (f : X' ⟶ X)
      [HasPullback i f] [IsH1RegularImmersion i] [Flat f],
      IsH1RegularImmersion (pullback.snd i f))

/- Lemma 76.44.5 (3): Let `S` be a scheme. Let `i : Z ⟶ X` be a quasi-regular
immersion of algebraic spaces over `S`. Let `f : X' ⟶ X` be a flat morphism of
algebraic spaces over `S`. Then `pullback.snd i f : Z ×[X] X' ⟶ X'` is a
quasi-regular immersion. -/
@[stacks 09RX] #check
  (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion.pullback_snd :
    ∀ {S : Scheme.{u}} {Z X X' : AlgebraicSpace S} (i : Z ⟶ X) (f : X' ⟶ X)
      [HasPullback i f] [IsQuasiRegularImmersion i] [Flat f],
      IsQuasiRegularImmersion (pullback.snd i f))
