module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.ClosedSubscheme
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.9.4: a closed immersion into a quasi-compact and quasi-separated scheme is a
directed limit, over the target, of closed immersions of finite presentation. -/
@[stacks 09ZP] #check
  (AlgebraicGeometry.Scheme.Limit.ClosedSubscheme.existsFinitePresentationLimit :
    ∀ {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
      [CompactSpace Y] [QuasiSeparatedSpace Y],
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ Over Y)
        (π : (Functor.const (OrderDual I)).obj (Over.mk i) ⟶ D),
        Nonempty (IsLimit (⟨Over.mk i, π⟩ : Cone D)) ∧
          ∀ j : I,
            IsClosedImmersion (D.obj j).hom ∧
              Scheme.Hom.FinitePresentation (D.obj j).hom)
