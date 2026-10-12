/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pushforward.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.FormalFiber.Serre
public import Mathlib.RingTheory.KrullDimension.Basic
import StacksCheckRecall

@[expose] public section

open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 51.12.1: for a locally Noetherian universally catenary scheme `X`, an
open subscheme `U`, and a coherent module `F` with `(S_n)` formal fibers along
the complement, the boundary depth-plus-point-closure-dimension condition is
equivalent to coherence of all higher direct images below `n`. -/
@[stacks 0BJY] #check
  (AlgebraicGeometry.Scheme.Modules.depth_add_pointClosureDim_gt_iff_higherDirectImage_isCoherent :
    ∀ {X : Scheme.{u}} [UniversallyCatenary X] (U : X.Opens)
      (F : U.toScheme.Modules) [F.IsCoherent] (n : ℕ),
      (∀ z : X, z ∉ U →
        (FieldAlgebraProperty.serreConditionS n).HoldsOnFormalFibers
          (X.presheaf.stalk z)) →
        ((∀ x : U, x ∈ RingedSpace.moduleSupport F →
          ∀ y : PointClosure.scheme (U.ι x),
            PointClosure.ι (U.ι x) y ∉ U →
              (.some (n : ℕ∞) : WithBot ℕ∞) <
                (.some (moduleDepth ((U : Scheme).presheaf.stalk x)
                  (RingedSpace.stalkModuleCat F x)) : WithBot ℕ∞) +
                    ringKrullDim
                      ((PointClosure.scheme (U.ι x)).presheaf.stalk y)) ↔
          ∀ p : ℕ, p < n →
            (RingedSpace.Hom.higherDirectImageModule U.ι.toShHom F p).IsCoherent))

end AlgebraicGeometry.Scheme.Modules
