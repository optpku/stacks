/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- Derived `m`-pseudo-coherence of a scheme module is equivalent to derived
`m`-pseudo-coherence after pullback along every member of an fppf cover. -/
theorem isMPseudoCoherent_iff_fppfCover
    {X : Scheme.{u}} (𝒰 : FppfCover.{u, v} X)
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ) :
    RingedSpace.ModuleDerived.IsMPseudoCoherent E m ↔
      ∀ i : 𝒰.I₀, RingedSpace.ModuleDerived.IsMPseudoCoherent
        ((RingedSpace.modulePullbackDerived (𝒰.f i).toLRSHom.toShHom).obj E) m := sorry

end AlgebraicGeometry.Scheme.ModuleDerived

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Derived `m`-pseudo-coherence of a complex with quasicoherent cohomology descends
along an fpqc covering family. -/
theorem isMPseudoCoherent_iff_fpqcCovering {X : Scheme.{u}} {ι : Type v}
    (family : ι → Over X) (hfamily : Scheme.FpqcCovering family)
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (m : ℤ) :
    RingedSpace.ModuleDerived.IsMPseudoCoherent E.obj m ↔
      ∀ i : ι, RingedSpace.ModuleDerived.IsMPseudoCoherent
        ((Scheme.DerivedQCoh.pullback (family i).hom).obj E).obj m := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
