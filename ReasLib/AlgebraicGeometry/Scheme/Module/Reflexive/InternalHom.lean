/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reflexivity of internal Homs

Internal Hom from a coherent module preserves reflexivity on an integral locally Noetherian
scheme.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- The dual of a coherent module is coherent. -/
instance instIsCoherentDual : (dual ℱ).IsCoherent := inferInstance

/-- The reflexive hull of a coherent module is coherent. -/
instance instIsCoherentReflexiveHull : (reflexiveHull ℱ).IsCoherent := inferInstance

end

section

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]

/-- If `ℱ` and `𝒢` are coherent modules on an integral locally Noetherian scheme and `𝒢` is
reflexive, then the internal Hom `internalHom ℱ 𝒢` is reflexive. -/
@[stacks 0AY4]
theorem isReflexive_internalHom (h𝒢 : IsReflexive 𝒢) :
    IsReflexive (internalHom ℱ 𝒢) := sorry

/-- The internal Hom from a coherent module to a coherent reflexive module is reflexive. -/
instance instIsReflexiveInternalHom [IsReflexive 𝒢] :
    IsReflexive (internalHom ℱ 𝒢) :=
  isReflexive_internalHom ℱ 𝒢 inferInstance

/-- The dual of a coherent module is reflexive. -/
instance instIsReflexiveDual : IsReflexive (dual ℱ) := inferInstance

/-- The reflexive hull of a coherent module is reflexive. -/
instance instIsReflexiveReflexiveHull : IsReflexive (reflexiveHull ℱ) := inferInstance

end

end AlgebraicGeometry.Scheme.Modules
