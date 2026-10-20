/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.EtaleComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.InternalHom
open CategoryTheory.MonoidalClosed
open Functor.PullbackInternalHom.Left
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Scheme.ModuleDerived.InternalHom
open Scheme.Etale.Small

noncomputable section

universe u

/- Lemma 86.2.3: let A be a Noetherian ring and X = Spec(A). Let 𝒪_étale be the
structure sheaf of X on the small étale site of X. Let K, L be objects of D(A).
If K ∈ D_Coh(A) and L has finite injective dimension, then
ε^* tilde RHom_A(K, L) = RSheafHom_{𝒪_étale}(ε^* tilde K, ε^* tilde L)
in D(𝒪_étale), where ε : (X_étale, 𝒪_étale) ⟶ (X, 𝒪_X) is the morphism of
ringed sites from Derived Categories of Spaces, Section 75.4, encoded as
schemeToZariskiDerived followed by exact pullback along smallEtaleToZariski. -/
@[stacks 0E50]
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.etaleAffineComparison_isIso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [RHom.Has (A := A)] (K L : DerivedCategory (ModuleCat.{u} A)),
      (∀ i : ℤ,
        Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) →
      DerivedCategory.HasFiniteInjectiveDimension L →
      IsIso (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.etaleAffineComparison K L))
