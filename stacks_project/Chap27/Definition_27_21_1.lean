module

public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

section

variable {S P : Scheme.{u}} {ℰ : S.Modules} [ℰ.IsQuasicoherent] {π : P ⟶ S}

/- Definition 27.21.1 (`01OB`).

For a quasi-coherent `ℰ : S.Modules`, a representation of `π : P ⟶ S` as its projective bundle
includes a relative projective-spectrum presentation and the invertible twists `𝒪_P(n)` for every
`n : ℤ`.
-/
@[stacks 01OB] #check
  (AlgebraicGeometry.Scheme.ProjectiveBundle.Representation π ℰ : Type (u + 1))

variable (hπ : AlgebraicGeometry.Scheme.ProjectiveBundle.Representation π ℰ)

#check (hπ.presentation : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation π)

#check (hπ.twist : ℤ → P.Modules)

#check (hπ.twist_isInvertible :
  ∀ n : ℤ, AlgebraicGeometry.Scheme.Modules.Invertible (hπ.twist n))

end
