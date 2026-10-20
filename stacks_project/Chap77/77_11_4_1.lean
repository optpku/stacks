/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flattening.InDimensions
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (ℱ : X.Modules) [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
variable (n : ℕ) (T : SchemeOver Y)

/- 77.11.4.1: the contravariant functor on schemes over `Y` is singleton precisely where
the base change of `ℱ` is flat over `T` in dimensions at least `n`, and empty otherwise. -/
@[stacks 0CWV] #check
  (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsFunctor f ℱ n :
    (SchemeOver Y)ᵒᵖ ⥤ Type u)

#check
  (Flattening.flatInDimensionsFunctor_nonempty_iff f ℱ n T :
    Nonempty ((Flattening.flatInDimensionsFunctor f ℱ n).obj (op T)) ↔
      Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f T.hom ℱ) (Limits.pullback.snd f T.hom) n)

#check
  (Flattening.flatInDimensionsFunctor_isEmpty_iff f ℱ n T :
    IsEmpty ((Flattening.flatInDimensionsFunctor f ℱ n).obj (op T)) ↔
      ¬ Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f T.hom ℱ) (Limits.pullback.snd f T.hom) n)

#check
  (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsFunctorObjSubsingleton f ℱ n T :
    Subsingleton ((Flattening.flatInDimensionsFunctor f ℱ n).obj (op T)))
