/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.FiniteSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 38.17.2 (1): for a separated finite-type morphism `f : X ⟶ S` and a finite-type
quasi-coherent module `F` whose support on every fibre is finite, relative purity,
finiteness of the scheme-theoretic support over `S`, and universal relative purity are
equivalent. -/
@[stacks 05K4]
#check
  (AlgebraicGeometry.Scheme.Modules.isPureOver_tfae_isFinite_schemeTheoreticSupport_isUniversallyPureOver :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [f.FiniteType] [IsSeparated f]
      (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
      (hfinite : ∀ s : S,
        (Scheme.Modules.moduleSupport
          ((Scheme.Modules.pullback (f.fiberι s)).obj F)).Finite),
      List.TFAE [
        F.IsPureOver f,
        IsFinite ((Scheme.Modules.schemeTheoreticSupport F).subschemeι ≫ f),
        F.IsUniversallyPureOver f])

/- Lemma 38.17.2 (2): under a quasi-finite separated morphism,
the source scheme is pure relative to the base exactly when the morphism is finite. -/
@[stacks 05K4]
#check
  (AlgebraicGeometry.Scheme.isPureOver_iff_isFinite_of_quasiFinite_of_isSeparated :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.QuasiFinite f] [IsSeparated f],
      Scheme.IsPureOver f ↔ IsFinite f)
