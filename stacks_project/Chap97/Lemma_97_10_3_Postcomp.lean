module

public import stacks_project.Chap97.Lemma_97_10_1_Sheaf

/-!
# Postcomposition of relative Hom

The morphism of fppf sheaves `Mor_B(Z, X') ⟶ Mor_B(Z, X)` induced by an
over-`B` morphism `X' ⟶ X`, acting objectwise by postcomposition on pairs.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X' X : Over B}

namespace HomPair

/-- Postcomposition with `f : X' ⟶ X` preserves the over-`B` triangle of a
relative-Hom pair. -/
theorem postcomp_w (f : X' ⟶ X) {T : Over S} (p : HomPair Z X' T) :
    (toOverMorph p ≫ f.left) ≫ X.hom = pullback.fst p.base Z.hom ≫ p.base :=
  sorry

/-- Postcomposition of a pair `(a, b)` along `f : X' ⟶ X`, sending `b` to
`b ≫ f.left` and leaving the test morphism `a` unchanged. -/
def postcomp (f : X' ⟶ X) {T : Over S} (p : HomPair Z X' T) : HomPair Z X T :=
  ofOverMorph p.base (toOverMorph p ≫ f.left) (postcomp_w f p)

/-- Postcomposition of pairs keeps the test morphism `a`. -/
theorem postcomp_base (f : X' ⟶ X) {T : Over S} (p : HomPair Z X' T) :
    (postcomp f p).base = p.base :=
  sorry

/-- Postcomposition of pairs sends `b` to `b ≫ f.left`. -/
theorem postcomp_toOverMorph (f : X' ⟶ X) {T : Over S} (p : HomPair Z X' T) :
    toOverMorph (postcomp f p) = toOverMorph p ≫ f.left :=
  sorry

end HomPair

/-- The presheaf morphism `Mor_B(Z, X') ⟶ Mor_B(Z, X)` induced by postcomposition
along `f : X' ⟶ X`. -/
def functorPostcomp (f : X' ⟶ X) : functor Z X' ⟶ functor Z X where
  app T := TypeCat.ofHom fun p ↦ HomPair.postcomp f p
  naturality := sorry

/-- Components of `functorPostcomp` are `HomPair.postcomp`. -/
theorem functorPostcomp_app (f : X' ⟶ X) (T : (Over S)ᵒᵖ)
    (p : HomPair Z X' T.unop) :
    (functorPostcomp f).app T p = HomPair.postcomp f p :=
  sorry

/-- The sheaf morphism `Mor_B(Z, X') ⟶ Mor_B(Z, X)` induced by postcomposition
along `f : X' ⟶ X`. -/
def postcomp (f : X' ⟶ X) : homSheaf Z X' ⟶ homSheaf Z X :=
  Sheaf.homEquiv.symm (functorPostcomp f)

/-- Components of `postcomp` are `HomPair.postcomp`. -/
theorem postcomp_app (f : X' ⟶ X) (T : (Over S)ᵒᵖ) (p : HomPair Z X' T.unop) :
    (postcomp f).hom.app T p = HomPair.postcomp f p :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
