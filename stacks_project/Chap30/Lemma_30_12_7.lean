/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Devissage
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 30.12.7

Let `X` be a Noetherian scheme and `Z₀` an irreducible closed subset with generic point `ξ`.
An extension-closed property of coherent modules which descends from positive finite
self-coproducts, holds for ideal pushforwards from proper integral closed subsets, and has the
specified generic model holds for every coherent module supported on `Z₀`.
-/
@[stacks 01YL] #check
  (AlgebraicGeometry.Scheme.Modules.devissage_property_of_support_subset_irreducibleClosed :
    ∀ {X : Scheme} [IsNoetherian X]
      (Z₀ : TopologicalSpace.IrreducibleCloseds X)
      (ξ : X) (hξ : IsGenericPoint ξ (Z₀ : Set X))
      (P : X.Modules → Prop)
      (h_shortExact : DevissageShortExactClosed P)
      (h_coproduct : DevissageDescendsFromFiniteCoproducts P)
      (h_proper_closed : DevissageHoldsOnProperIntegralIdealPushforwards Z₀ P)
      (h_generic_model : DevissageGenericModel Z₀ ξ P)
      (ℱ : X.Modules) [ℱ.IsCoherent]
      (hSupp : moduleSupport ℱ ⊆ (Z₀ : Set X)),
      P ℱ)

end AlgebraicGeometry.Scheme.Modules
