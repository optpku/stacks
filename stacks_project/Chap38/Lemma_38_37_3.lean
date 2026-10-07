module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup.Approximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 38.37.3: for an almost blowup square over a quasi-compact and
quasi-separated scheme `X`, the canonical strict transform is the limit in `Over X'`
of a directed inverse system of finite-presentation closed subschemes whose composites
to `X` are again almost blowup squares. -/
@[stacks 0EV9] #check
  (AlgebraicGeometry.IsAlmostBlowupSquare.existsFinitePresentationLimit :
    ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (b : X' ⟶ X) (I : X.IdealSheafData)
      (hSquare : AlgebraicGeometry.IsAlmostBlowupSquare b I) [CompactSpace X]
      [QuasiSeparatedSpace X],
      ∃ (ι : Type u) (_ : Preorder ι) (_ : Nonempty ι) (_ : IsDirected ι (· ≤ ·))
        (D : OrderDual ι ⥤ Over X')
        (π : (Functor.const (OrderDual ι)).obj
          (Over.mk (AlgebraicGeometry.strictTransformSnd b (I.comap b) (𝟙 X))) ⟶ D),
        Nonempty
            (IsLimit
              (⟨Over.mk (AlgebraicGeometry.strictTransformSnd b (I.comap b) (𝟙 X)), π⟩ :
                Cone D)) ∧
          ∀ j : ι,
            AlgebraicGeometry.IsClosedImmersion (D.obj j).hom ∧
              AlgebraicGeometry.Scheme.Hom.FinitePresentation (D.obj j).hom ∧
                AlgebraicGeometry.IsAlmostBlowupSquare ((D.obj j).hom ≫ b) I)
