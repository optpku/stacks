module

public import stacks_project.Chap67.Lemma_67_21_6_QuasiAffine
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.21.6: let `S` be a scheme. A quasi-compact and quasi-separated morphism
of algebraic spaces `f : X ⟶ Y` over `S` is quasi-affine if and only if the
canonical factorization `Hom.toPushforwardRelativeSpec f :
X ⟶ relativeSpec (pushforwardStructureQcAlgebra f)` is an open immersion. -/
@[stacks 086S] #check
  (QuasiAffine.iff_isOpenImmersion_toPushforwardRelativeSpec :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f],
      QuasiAffine f ↔ IsOpenImmersion (Hom.toPushforwardRelativeSpec f))
