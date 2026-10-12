/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap38.«38_20_7_2_Functor»
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {X S : Scheme.{u}}
variable (f : X ⟶ S) (ℱ : X.Modules) (p : ℕ)
variable [Smooth f] [GeometricallyIrreducible f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
variable (T : Over S)

/- Situation 38.20.7: the rank-p freeness condition at every fibre generic point
defines a subterminal contravariant functor on schemes over S. -/
@[stacks 05MP] #check
  (AlgebraicGeometry.Scheme.Flattening.freeAtGenericPointsFunctor f ℱ p :
    (Over S)ᵒᵖ ⥤ Type u)

#check Scheme.Modules.baseChangeModule f T.hom ℱ

#check (inferInstance : Smooth (pullback.snd f T.hom))

#check (inferInstance : GeometricallyIrreducible (pullback.snd f T.hom))

#check Scheme.Flattening.IsFreeAtGenericPoints f ℱ p T

#check Scheme.Flattening.IsFreeAtGenericPoints.pullback

#check Scheme.Flattening.freeAtGenericPointsFunctor_nonempty_iff f ℱ p T
