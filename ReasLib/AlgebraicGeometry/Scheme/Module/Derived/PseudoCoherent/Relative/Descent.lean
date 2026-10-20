module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Flat

/-!
# Fppf descent of relative pseudo-coherence

Relative pseudo-coherence of derived modules with quasi-coherent cohomology can
be tested after pullback along the members of an fppf cover.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver

/-- Relative `m`-pseudo-coherence over a locally finite type morphism is equivalent
to relative `m`-pseudo-coherence of every derived pullback along an fppf cover. -/
theorem iff_fppfCover {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (𝒰 : FppfCover.{u, v} X) (E : Scheme.DerivedQCoh X) (m : ℤ) :
    IsMPseudoCoherentOver f E.obj m ↔
      ∀ i : 𝒰.I₀, @IsMPseudoCoherentOver _ _ (𝒰.f i ≫ f)
        (FppfCover.locallyOfFiniteType_comp f 𝒰 i)
        ((Scheme.DerivedQCoh.pullback (𝒰.f i)).obj E).obj m := sorry

/-- Relative `m`-pseudo-coherence over a locally finite type morphism is equivalent to
relative `m`-pseudo-coherence after every base change along an fppf cover of the target. -/
theorem iff_fppfCover_target {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (𝒰 : FppfCover.{u, v} S) (E : Scheme.DerivedQCoh X) (m : ℤ) :
    IsMPseudoCoherentOver f E.obj m ↔
      ∀ i : 𝒰.I₀, IsMPseudoCoherentOver (pullback.snd f (𝒰.f i))
        ((Scheme.DerivedQCoh.pullback (pullback.fst f (𝒰.f i))).obj E).obj m := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver
