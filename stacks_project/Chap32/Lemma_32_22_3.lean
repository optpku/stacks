module

import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.SchemeTheoreticImage
import StacksCheckRecall

open CategoryTheory Limits

noncomputable section

universe u

/- Lemma 32.22.3: a quasi-separated finite-type scheme is the limit of the compatible
tail system of its scheme-theoretic images in a finite-type approximation. -/
@[stacks 0CNQ] #check
  (AlgebraicGeometry.FiniteTypeApproximationDiagram.nonempty_isLimit_schemeTheoreticImageCone :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ AlgebraicGeometry.Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, AlgebraicGeometry.IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'),
        AlgebraicGeometry.IsAffineHom (D.map (homOfLE hjj'))]
      (i : I) {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ c.pt)
      [AlgebraicGeometry.QuasiSeparated f] [AlgebraicGeometry.Scheme.Hom.FiniteType f]
      (approximation :
        AlgebraicGeometry.FiniteTypeApproximationDiagram f (c.π.app i))
      [AlgebraicGeometry.Scheme.Hom.FiniteType approximation.toSi]
      [AlgebraicGeometry.IsClosedImmersion
        (pullback.lift f approximation.toW approximation.w.symm)]
      (Xi : Over (show OrderDual I from i) ⥤ AlgebraicGeometry.Scheme.{u})
      (π : (Functor.const (Over (show OrderDual I from i))).obj X ⟶ Xi)
      (ι : Xi ⟶ AlgebraicGeometry.Scheme.baseChangeOverDiagram D
        (show OrderDual I from i) approximation.toSi)
      (himage : ∀ j : Over (show OrderDual I from i),
        AlgebraicGeometry.IsSchemeTheoreticImageFactorization
          ((approximation.baseChangeCone D c).π.app j) (π.app j) (ι.app j)),
      Nonempty (IsLimit (⟨X, π⟩ : Cone Xi)))
