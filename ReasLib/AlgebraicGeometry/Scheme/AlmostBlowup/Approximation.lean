module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Limit.ClosedSubscheme

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.IsAlmostBlowupSquare

/-- Over a quasi-compact and quasi-separated scheme, the canonical strict transform of an almost
blowup square is the limit of a nonempty directed inverse system of finite-presentation closed
subschemes whose composites with the original morphism are again almost blowup squares. -/
theorem existsFinitePresentationLimit
    {X X' : Scheme.{u}} (b : X' ⟶ X) (I : X.IdealSheafData)
    (hSquare : IsAlmostBlowupSquare b I) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : Nonempty ι) (_ : IsDirected ι (· ≤ ·))
      (D : OrderDual ι ⥤ Over X')
      (π : (Functor.const (OrderDual ι)).obj
        (Over.mk (strictTransformSnd b (I.comap b) (𝟙 X))) ⟶ D),
      Nonempty (IsLimit (⟨Over.mk (strictTransformSnd b (I.comap b) (𝟙 X)), π⟩ : Cone D)) ∧
        ∀ j : ι,
          IsClosedImmersion (D.obj j).hom ∧
            Scheme.Hom.FinitePresentation (D.obj j).hom ∧
              IsAlmostBlowupSquare ((D.obj j).hom ≫ b) I := sorry

end AlgebraicGeometry.IsAlmostBlowupSquare
