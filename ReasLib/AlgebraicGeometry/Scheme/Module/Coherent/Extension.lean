/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Restriction

/-!
# Extension of morphisms between coherent modules

Morphisms between restrictions of coherent modules to an open subscheme extend from a
coherent submodule of the source on a locally Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A morphism between the restrictions of two coherent modules to an open subscheme extends
to the target from a coherent subobject of the source whose inclusion restricts to an
isomorphism. -/
theorem exists_coherentSubobject_extension_of_restrict_hom
    (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
    (U : X.Opens)
    (φ : ((Scheme.Modules.restrictFunctor U.ι).obj ℱ) ⟶
      ((Scheme.Modules.restrictFunctor U.ι).obj 𝒢)) :
    ∃ (ℱ' : Subobject ℱ), ∃ (_ : ((ℱ' : X.Modules)).IsCoherent),
      ∃ (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map ℱ'.arrow)),
        ∃ φ' : (ℱ' : X.Modules) ⟶ 𝒢,
          (Scheme.Modules.restrictFunctor U.ι).map φ' =
            (Scheme.Modules.restrictFunctor U.ι).map ℱ'.arrow ≫ φ := sorry

end AlgebraicGeometry.Scheme.Modules
