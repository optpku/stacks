/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Functoriality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-isomorphisms and the ideal-sheaf eta functor

The Berthelot-Ogus eta construction preserves quasi-isomorphisms on its canonical domain.
The result is stated first for the underlying cochain map and then for the bundled eta functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf.Eta

variable {X : RingedSpace.{u}}
variable (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
variable [isInvertibleObject (I : X.Modules)]

/-- The eta map induced by a quasi-isomorphism between complexes with degreewise monic
`I`-action is a quasi-isomorphism. -/
theorem map_quasiIso {K L : CochainComplex X.Modules ℤ} (φ : K ⟶ L)
    [IsActionMono.Complex I K] [IsActionMono.Complex I L] [QuasiIso φ] :
    QuasiIso (map I φ) := sorry

/-- Lemma 20.55.6 (0F8P): the eta functor preserves quasi-isomorphisms between complexes in its
canonical degreewise action-monic domain. -/
@[stacks 0F8P, instance]
theorem functor_map_quasiIso {K L : Domain I} (φ : K ⟶ L) [QuasiIso φ.hom] :
    QuasiIso ((functor I).map φ) := sorry

end AlgebraicGeometry.RingedSpace.IdealSheaf.Eta
