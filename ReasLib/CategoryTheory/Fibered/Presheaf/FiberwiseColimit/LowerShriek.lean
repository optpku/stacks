/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Presheaf.FiberwiseColimit.Sheaf
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiberwise colimits and lower shriek

For the inherited topology of a fibered projection, its lower shriek is computed by sheafifying
the topology-independent fiberwise-colimit presheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v wX vX a b

namespace CategoryTheory.FiberedCategoryOver.Presheaf.fiberwiseColimit

variable {C : Type u} [Category.{v} C]
variable (X : FiberedCategoryOver.{u, v, wX, vX} C)
variable (A : Type a) [Category.{b} A]
variable (J : GrothendieckTopology C)
variable [∀ V : C, HasColimitsOfShape (X.p.Fiber V)ᵒᵖ A]
variable [HasWeakSheafify J A]
variable [
  (X.p.sheafPushforwardContinuous A (X.p.inheritedTopology J) J).IsRightAdjoint]

/-- The sheafified fiberwise-colimit functor is left adjoint to pushforward along the projection. -/
@[stacks 08PE "sheafified fiberwise-colimit adjunction"]
noncomputable def sheafAdjunction :
    sheafFunctor X A (X.p.inheritedTopology J) J ⊣
      X.p.sheafPushforwardContinuous A (X.p.inheritedTopology J) J :=
  ((adjunction X A).comp (sheafificationAdjunction J A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (X.p.inheritedTopology J) A)
    (Functor.FullyFaithful.id _) (Iso.refl _)
    (X.p.sheafPushforwardContinuousCompSheafToPresheafIso A
      (X.p.inheritedTopology J) J).symm

/-- Lemma 21.38.8 (08PE): projection lower shriek is canonically isomorphic to the
sheafified fiberwise-colimit functor. -/
@[stacks 08PE]
noncomputable def lowerShriekIso :
    X.p.sheafPullback A (X.p.inheritedTopology J) J ≅
      sheafFunctor X A (X.p.inheritedTopology J) J :=
  Adjunction.leftAdjointUniq
    (X.p.sheafAdjunctionContinuous A (X.p.inheritedTopology J) J)
    (sheafAdjunction X A J)

/-- Object component of the canonical fiberwise-colimit computation of projection lower shriek. -/
@[stacks 08PE "projection lower shriek on an object"]
noncomputable def lowerShriekObjIso
    (F : Sheaf (X.p.inheritedTopology J) A) :
    (X.p.sheafPullback A (X.p.inheritedTopology J) J).obj F ≅
      sheaf X A (X.p.inheritedTopology J) J F :=
  (lowerShriekIso X A J).app F

end CategoryTheory.FiberedCategoryOver.Presheaf.fiberwiseColimit
