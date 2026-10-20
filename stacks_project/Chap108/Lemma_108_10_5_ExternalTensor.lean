module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback

/-!
# External tensor products of modules on algebraic spaces

The canonical external tensor product `p₁^* F ⊗ p₂^* G` on a fibre product
of algebraic spaces over a common base.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The external tensor product `p₁^* F ⊗ p₂^* G` on the fibre product of two
algebraic spaces over a common base. -/
abbrev externalTensorProduct {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (F : X.Modules) (G : Y.Modules) :
    (Limits.pullback f g).Modules :=
  tensorObj ((pullback (Limits.pullback.fst f g)).obj F)
    ((pullback (Limits.pullback.snd f g)).obj G)

/-- `externalTensorProduct f g F G` is the tensor of the pullbacks of `F` and
`G` along the projections of the fibre product. -/
theorem externalTensorProduct_eq {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (F : X.Modules) (G : Y.Modules) :
    externalTensorProduct f g F G =
      (pullback (Limits.pullback.fst f g)).obj F ⊗
        (pullback (Limits.pullback.snd f g)).obj G :=
  sorry

/-- The external tensor product of invertible modules is invertible. -/
instance instIsInvertibleObject_externalTensorProduct
    {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B)
    (F : X.Modules) (G : Y.Modules) [isInvertibleObject F] [isInvertibleObject G] :
    isInvertibleObject (externalTensorProduct f g F G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
