/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.RepresentedBy
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Rigidified.PushforwardLine
public import ReasLib.AlgebraicGeometry.Hilbert.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RigidifiedPicard

/-- For a smooth projective geometrically irreducible curve with a rational section,
the pushforward-line subfunctor is represented by an open of the canonical degree-genus
Hilbert scheme. -/
theorem pushforwardLineSubfunctor_representableByOpenHilbertSubscheme
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    (σ : Spec (CommRingCat.of k) ⟶ X.left) (hσ : σ ≫ X.hom = 𝟙 _)
    (g : ℕ) (h_genus : Curve.genus X = g) :
    ∃ (U : (Hilbert.functor X g).reprX.left.Opens)
      (ξU : (pushforwardLineSubfunctor X σ hσ).toFunctor.obj
        (op (Over.mk (U.ι ≫ (Hilbert.functor X g).reprX.hom)))),
      (pushforwardLineSubfunctor X σ hσ).toFunctor.IsRepresentedBy ξU := sorry

end AlgebraicGeometry.RigidifiedPicard
