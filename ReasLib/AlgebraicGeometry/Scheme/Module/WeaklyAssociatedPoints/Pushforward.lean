/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Affine
import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.Restriction

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- A point outside the range of a quasi-compact and quasi-separated scheme morphism is not
weakly associated to the pushforward of a quasi-coherent module. -/
theorem not_mem_weakAss_pushforward_of_not_mem_range
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (s : S) (hs : s ∉ Set.range f.base) :
    s ∉ ((Scheme.Modules.pushforward f).obj ℱ).weakAss := sorry

/-- Under an affine morphism, every weakly associated point of the pushforward of a
quasi-coherent module is the image of a weakly associated point of the module. -/
theorem weakAss_pushforward_subset_image_of_isAffine
    (f : X ⟶ S) [AlgebraicGeometry.IsAffineHom f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj ℱ).weakAss ⊆ f.base '' ℱ.weakAss := sorry

/-- Under a finite morphism, the weakly associated points of the pushforward of a
quasi-coherent module are exactly the images of its weakly associated points. -/
@[stacks 05EZ]
theorem weakAss_pushforward_eq_image_of_isFinite
    (f : X ⟶ S) [IsFinite f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj ℱ).weakAss = f.base '' ℱ.weakAss := sorry

end AlgebraicGeometry.Scheme.Modules
