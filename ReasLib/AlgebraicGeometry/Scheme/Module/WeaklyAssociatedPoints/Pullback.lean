module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.StandardEtale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Pushforward

/-!
# Weakly associated points under pullback
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A pointwise-flat morphism pulls a weakly associated point of a quasi-coherent module back to
a weakly associated point when the source point is generic in its scheme-theoretic fiber. -/
theorem mem_weakAss_pullback_of_flatAt_of_isGenericPoint_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (𝒢 : S.Modules) [𝒢.IsQuasicoherent] (x : X)
    (hflat : Scheme.Hom.flatAt f x)
    (hgeneric : f.asFiber x ∈ genericPoints (f.fiber (f x)))
    (hs : f x ∈ 𝒢.weakAss) :
    x ∈ ((Scheme.Modules.pullback f).obj 𝒢).weakAss := sorry

/-- For a finite flat morphism, a point is weakly associated to the pullback of a
quasicoherent module if and only if its image is weakly associated to the original module. -/
@[stacks 05FN]
theorem mem_weakAss_pullback_iff_of_isFinite_of_flat {T S : Scheme.{u}}
    (g : T ⟶ S) [IsFinite g] [Flat g] (𝒢 : S.Modules) [𝒢.IsQuasicoherent] (t : T) :
    t ∈ ((Scheme.Modules.pullback g).obj 𝒢).weakAss ↔ g t ∈ 𝒢.weakAss := sorry

/-- For an étale morphism, a point is weakly associated to the pullback of a
quasicoherent module if and only if its image is weakly associated to the original module. -/
@[stacks 05FP]
theorem mem_weakAss_pullback_iff_of_etale {U S : Scheme.{u}} (h : U ⟶ S) [Etale h]
    (𝒢 : S.Modules) [𝒢.IsQuasicoherent] (u : U) :
    u ∈ ((Scheme.Modules.pullback h).obj 𝒢).weakAss ↔ h u ∈ 𝒢.weakAss := sorry

end AlgebraicGeometry.Scheme.Modules
