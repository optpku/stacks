/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_52_2
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.34.2 (1): `Hom.toNormalization f` is an open immersion. -/
@[stacks 082J] #check
  (Hom.instIsOpenImmersionToNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiFinite f] [Separated f],
      IsOpenImmersion (Hom.toNormalization f))

/- Lemma 76.34.2 (2): `Hom.toNormalization f` is quasi-compact. -/
@[stacks 082J] #check
  (Hom.instQuasiCompactToNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiFinite f] [Separated f],
      QuasiCompact (Hom.toNormalization f))

/- Lemma 76.34.2 (3): `Hom.fromNormalization f` is integral. -/
@[stacks 082J] #check
  (Hom.instIsIntegralHomFromNormalization :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiFinite f] [Separated f],
      IsIntegralHom (Hom.fromNormalization f))

/- Lemma 76.34.2 (4): in particular `f` is quasi-affine. -/
@[stacks 082J] #check
  (QuasiFinite.instQuasiAffine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiFinite f] [Separated f],
      QuasiAffine f)
