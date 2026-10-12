/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.UniversallyInjective
public import stacks_project.Chap35.«35_4_20_1»
public import stacks_project.Chap35.Definition_35_4_19_Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

namespace ModuleCat.DescentPushforward

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The canonical equalizer fork whose point computes descent pushforward. -/
noncomputable abbrev equalizerFork (f : R →+* S)
    (D : (ModuleCat.extendRestrictScalarsAdj.{w} f).toComonad.Coalgebra) :
    Fork ((ModuleCat.restrictScalars f).map D.a)
      ((ModuleCat.extendRestrictScalarsAdj f).unit.app
        ((ModuleCat.restrictScalars f).obj D.A)) := fork f D

/- Lemma 35.4.20: if `algebraMap R S` is universally injective, then extending
scalars to `S` carries the descent-pushforward equalizer fork to a limiting fork.
Under the canonical tensor identifications, this is the displayed diagram whose
arrows are induced by the descent datum `θ` and the coface maps `δ₀¹`, `δ₁¹`,
`δ₀²`, `δ₁²`, and `δ₂²`. -/
@[stacks 08X7] #check
  (ModuleCat.DescentPushforward.baseChangeIsLimit :
    ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
      (_ : LinearMap.UniversallyInjective (Algebra.linearMap R S))
      (D : (ModuleCat.extendRestrictScalarsAdj.{u}
        (algebraMap R S)).toComonad.Coalgebra),
      Nonempty (IsLimit (Fork.ofCone
        ((ModuleCat.extendScalars (algebraMap R S)).mapCone
          (equalizerFork (algebraMap R S) D)))))

end ModuleCat.DescentPushforward
