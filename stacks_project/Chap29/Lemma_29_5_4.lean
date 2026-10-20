/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/- Lemma 29.5.4 (1): The affine annihilators of `ℱ` define its smallest closed subscheme,
and `ℱ` is the pushforward of a quasicoherent module from a closed subscheme exactly when
that subscheme contains this canonical one. -/
@[stacks 05JU] #check
  (schemeTheoreticSupport_spec ℱ :
    IsSchemeTheoreticSupport ℱ (schemeTheoreticSupport ℱ) ∧
      ∀ J : X.IdealSheafData,
        (∃ 𝒢 : J.subscheme.Modules,
          ∃ _ : 𝒢.IsQuasicoherent,
            Nonempty ((Scheme.Modules.pushforward J.subschemeι).obj 𝒢 ≅ ℱ)) ↔
          J ≤ schemeTheoreticSupport ℱ)

/- Lemma 29.5.4 (2): The ordinary support of `ℱ` is the underlying closed set of its
scheme-theoretic support. -/
@[stacks 05JU] #check
  (moduleSupport_eq_of_isSchemeTheoreticSupport ℱ (schemeTheoreticSupport ℱ)
      (schemeTheoreticSupport_isSchemeTheoreticSupport ℱ) :
    RingedSpace.moduleSupport ℱ = ((schemeTheoreticSupport ℱ).support : Set X))

/- Lemma 29.5.4 (3): The module `ℱ` descends to a finite-type quasicoherent module of full
support on its scheme-theoretic support. -/
@[stacks 05JU] #check
  (exists_finiteType_module_of_isSchemeTheoreticSupport ℱ (schemeTheoreticSupport ℱ)
      (schemeTheoreticSupport_isSchemeTheoreticSupport ℱ) :
    ∃ 𝒢 : (schemeTheoreticSupport ℱ).subscheme.Modules,
      ∃ _ : 𝒢.IsQuasicoherent,
        ∃ _ : 𝒢.IsFiniteType,
          Nonempty
              ((Scheme.Modules.pushforward (schemeTheoreticSupport ℱ).subschemeι).obj 𝒢 ≅ ℱ) ∧
            RingedSpace.moduleSupport 𝒢 = Set.univ)

variable (𝒢 𝒢' : (schemeTheoreticSupport ℱ).subscheme.Modules)
  [𝒢.IsQuasicoherent] [𝒢'.IsQuasicoherent]
  (e : (Scheme.Modules.pushforward (schemeTheoreticSupport ℱ).subschemeι).obj 𝒢 ≅ ℱ)
  (e' : (Scheme.Modules.pushforward (schemeTheoreticSupport ℱ).subschemeι).obj 𝒢' ≅ ℱ)

/- Lemma 29.5.4 (4): Two quasicoherent descents of `ℱ` to its scheme-theoretic support are
uniquely isomorphic compatibly with their chosen pushforward identifications. -/
@[stacks 05JU] #check
  (existsUnique_iso_of_pushforward_iso ℱ (schemeTheoreticSupport ℱ) 𝒢 𝒢' e e' :
    ∃! α : 𝒢 ≅ 𝒢',
      ((Scheme.Modules.pushforward (schemeTheoreticSupport ℱ).subschemeι).mapIso α).trans e' = e)

end AlgebraicGeometry.Scheme.Modules
