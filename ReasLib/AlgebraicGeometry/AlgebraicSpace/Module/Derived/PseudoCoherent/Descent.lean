module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A derived module with quasi-coherent cohomology on an algebraic space is
`m`-pseudo-coherent if and only if its derived pullback along every member of
an fpqc covering is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_iff_fpqcCovering {S : Scheme.{u}} {X : AlgebraicSpace S}
    {ι : Type v} (family : ι → Over X) (hfamily : FpqcCovering family)
    (E : ModuleDerived X) (hE : derivedQuasiCoherentModuleProperty X E) (m : ℤ) :
    IsMPseudoCoherent X E m ↔
      ∀ i, IsMPseudoCoherent (family i).left
        ((ModuleDerived.pullback (family i).hom).obj E) m := sorry

end AlgebraicGeometry.AlgebraicSpace
