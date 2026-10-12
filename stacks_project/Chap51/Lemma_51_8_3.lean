/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import Mathlib.RingTheory.KrullDimension.Basic
public import stacks_project.Chap51.Lemma_51_8_1
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.OpenImmersion
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 51.8.3: let `X` be a locally Noetherian, Nagata, universally catenary scheme,
`U` an open subscheme, and `ℱ` a coherent `𝒪_U`-module. If the local ring of the
reduced closure of every `x ∈ ℱ.associatedPoints` has dimension at least two at each
point outside `U`, then the pushforward of `ℱ` along `U.ι` is coherent. -/
@[stacks 0AWA] #check
  (AlgebraicGeometry.Scheme.Modules.pushforward_obj_isCoherent_of_two_le_pointClosure_stalk :
    ∀ {X : Scheme.{u}} [Nagata X] [UniversallyCatenary X]
      (U : X.Opens) (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent],
      (∀ x : U, x ∈ ℱ.associatedPoints → ∀ z : PointClosure.scheme (U.ι x),
        PointClosure.ι (U.ι x) z ∉ U →
          2 ≤ ringKrullDim ((PointClosure.scheme (U.ι x)).presheaf.stalk z)) →
      ((pushforward U.ι).obj ℱ).IsCoherent)

end AlgebraicGeometry.Scheme.Modules
