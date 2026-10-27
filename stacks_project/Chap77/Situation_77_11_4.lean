/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flattening.InDimensions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.LocalGeneration
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (ℱ : X.Modules) [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
variable (n : ℕ) (T : SchemeOver Y)

/- Situation 77.11.4: for a locally finite type morphism of algebraic spaces and a
finite-type quasi-coherent module, base change defines a subterminal contravariant
functor on schemes over `Y`, recording where the pullback is flat over the new base
in dimensions at least `n`. -/
@[stacks 0CWU] #check
  (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsFunctor f ℱ n :
    (SchemeOver Y)ᵒᵖ ⥤ Type u)

#check
  (Modules.baseChangeSpace f T.hom : AlgebraicSpace S)

#check
  (Modules.baseChangeProj f T.hom : Modules.baseChangeSpace f T.hom ⟶ X)

#check
  (Modules.baseChangeModule f T.hom ℱ : (Modules.baseChangeSpace f T.hom).Modules)

#check
  (Limits.pullback.snd f T.hom : Modules.baseChangeSpace f T.hom ⟶ ofOver T.left)

#check
  (inferInstance : LocallyOfFiniteType (Limits.pullback.snd f T.hom))

#check
  (inferInstance : (Modules.baseChangeModule f T.hom ℱ).IsFiniteType)

#check
  (Modules.flatOverInDimensionsGE
    (Modules.baseChangeModule f T.hom ℱ) (Limits.pullback.snd f T.hom) n : Prop)

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
  (Flattening.flatInDimensionsFunctorObjSubsingleton f ℱ n T :
    Subsingleton ((Flattening.flatInDimensionsFunctor f ℱ n).obj (op T)))
