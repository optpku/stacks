module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.NonregularQuotient
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.PuncturedSpectrum

universe u

/-
The quotient `A = k[[a,b,x,y,z,u,v,w]]/(a³,b³,xa² + yab + zb²,w²)`
has a nontrivial punctured-spectrum Picard group despite having eight ambient
variables and four relations. Thus the dimension-only condition `dim(B) - r ≥ 4`
does not replace the regular-sequence hypothesis in Proposition 52.27.6.
-/

/- Example 52.27.8 (1): the five-variable quotient has depth zero, witnessed by the
nonzero class `a^2 b^2` annihilated by all five coordinates. -/
@[stacks 0F9L] #check
  (AlgebraicGeometry.PuncturedSpectrum.NonregularQuotient.depth_ring1 :
    ∀ {k : Type u} [Field k],
      moduleDepth (NonregularQuotient.Ring1 k) (NonregularQuotient.Ring1 k) = 0)

/- Example 52.27.8 (2): the seven-variable quotient `A₀` has depth two. -/
@[stacks 0F9L] #check
  (AlgebraicGeometry.PuncturedSpectrum.NonregularQuotient.depth_ring0 :
    ∀ {k : Type u} [Field k],
      moduleDepth (NonregularQuotient.Ring0 k) (NonregularQuotient.Ring0 k) = 2)

/- Example 52.27.8 (3): the Picard group of the punctured spectrum of `Ring k` is
not subsingleton. -/
@[stacks 0F9L] #check
  (AlgebraicGeometry.PuncturedSpectrum.NonregularQuotient.picardGroup_not_subsingleton :
    ∀ {k : Type u} [Field k],
      ¬ Subsingleton (Scheme.PicardGroup (PuncturedSpectrum.scheme (NonregularQuotient.Ring k))))
