module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Pullback

universe u

/- Lemma 31.6.4: for a morphism of schemes `f : X ⟶ S`, a quasi-coherent
`𝒪_S`-module `𝒢`, and a point `x : X`, if `f` is flat at `x`, `x` is generic in the fiber over
`f x`, and `f x` is weakly associated to `𝒢`, then `x` is weakly associated to the pullback of
`𝒢`. -/
@[stacks 05F0] #check
  (AlgebraicGeometry.Scheme.Modules.mem_weakAss_pullback_of_flatAt_of_isGenericPoint_fiber :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (𝒢 : S.Modules)
      [𝒢.IsQuasicoherent] (x : X),
      AlgebraicGeometry.Scheme.Hom.flatAt f x →
        f.asFiber x ∈ genericPoints (f.fiber (f x)) →
          f x ∈ 𝒢.weakAss →
            x ∈ ((AlgebraicGeometry.Scheme.Modules.pullback f).obj 𝒢).weakAss)
