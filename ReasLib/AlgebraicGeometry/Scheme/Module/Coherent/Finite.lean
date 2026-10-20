module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherent modules and finite morphisms

Finite morphisms preserve coherence under pushforward over locally Noetherian schemes.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Pushforward along a finite morphism to a locally Noetherian scheme carries coherent modules
to coherent modules. -/
@[stacks 01Y6, instance]
theorem pushforward_obj_isCoherent_of_isFinite
    (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    ((Scheme.Modules.pushforward f).obj ℱ).IsCoherent := sorry

/-- For a finite surjective morphism to a locally Noetherian scheme and an integral closed
subscheme of the target, there is a coherent module on the source whose pushforward has exactly
the prescribed support and whose generic stalk is annihilated by the maximal ideal. -/
@[stacks 01YO]
theorem exists_coherent_pushforward_support_eq_and_stalk_annihilated
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsLocallyNoetherian X]
    (Z : X.IdealSheafData) [IsIntegral Z.subscheme]
    (ξ : X) (hξ : IsGenericPoint ξ (Z.support : Set X)) :
    ∃ ℱ : Y.Modules,
      ∃ _ : ℱ.IsCoherent,
        ∃ _ : RingedSpace.moduleSupport ((Scheme.Modules.pushforward f).obj ℱ) =
            (Z.support : Set X),
          ∀ r : X.presheaf.stalk ξ,
            r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) →
              ∀ m : RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) ξ,
                r • m = 0 := sorry

end AlgebraicGeometry.Scheme.Modules
