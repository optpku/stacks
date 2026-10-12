/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Square
import StacksCheckRecall

/-!
# 15.7.1.1

@stack 08KL
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.CategoricalPullback

universe u

section

variable {C D Cp Dp : Type u}
variable [CommRing C] [CommRing D] [CommRing Cp] [CommRing Dp]
variable (f : D →+* C) (g : Cp →+* C) (p : Dp →+* D) (q : Dp →+* Cp)

/- Domain-style sampling for 15.7.1.1:
- primary domain: categorical base change for module categories over a commuting square of
  commutative rings;
- sampled owner abstractions:
  `ModuleCat.extendScalarsComp`,
  `ModuleCat.extendScalarsCommSq`,
  `ModuleCat.extendScalarsToPullback`,
  `CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback`;
- best owner abstraction: the shared owner `ModuleCat.extendScalarsCommSq`;
- primitive data: the commuting square of ring maps `Dp → D`, `Dp → Cp`, `D → C`, `Cp → C`,
  given by `p`, `q`, `f`, `g`, and a proof `f.comp p = g.comp q`;
- derived API: the induced functor `ModuleCat.extendScalarsToPullback`, and the
  comparison isomorphism read directly as `(ModuleCat.extendScalarsCommSq f g p q hcomm).iso`.

Source/core/bridge triage:
- `source-facing`: the specialized checks below;
- `core/canonical`: `CatCommSqOver`;
- `bridge/view`: `ModuleCat.extendScalarsToPullback`. -/

/- 15.7.1.1: for a commuting square of commutative rings `Dp → D`, `Dp → Cp`, `D → C`, and
`Cp → C`, the categorical base-change square of extension-of-scalars functors is the specialization
of the shared owner `ModuleCat.extendScalarsCommSq`. -/
@[stacks 08KL "module-category base-change square"]
#check ModuleCat.extendScalarsCommSq

variable (hcomm : f.comp p = g.comp q)

/- Specialized square for the ring maps `p`, `q`, `f`, `g`. -/
#check (ModuleCat.extendScalarsCommSq f g p q hcomm)

/- The induced functor
`Mod_{Dp} → Mod_D ×_[Mod_C] Mod_{Cp}` is the corresponding owner-derived pullback functor. -/
#check ModuleCat.extendScalarsToPullback

/- Companion specialization to the same commuting square. -/
#check (ModuleCat.extendScalarsToPullback f g p q hcomm)

/- The canonical base-change comparison between the two iterated extension-of-scalars functors is
the `iso` field of the owner square. -/
#check ((ModuleCat.extendScalarsCommSq f g p q hcomm).iso :
  ModuleCat.extendScalars p ⋙ ModuleCat.extendScalars f ≅
    ModuleCat.extendScalars q ⋙ ModuleCat.extendScalars g)

variable (L : ModuleCat Dp)

/- The structural isomorphism on an object of the specialized pullback functor is definitionally
the component of that canonical comparison. -/
#check (((ModuleCat.extendScalarsToPullback f g p q hcomm).obj L).iso :
  (ModuleCat.extendScalars f).obj ((ModuleCat.extendScalars p).obj L) ≅
    (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars q).obj L))

end
