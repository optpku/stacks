module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity.FieldExtension
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.35.8: for a field extension `k'/k`, a coherent module sheaf on standard projective
`n`-space is `m`-regular if and only if its canonical field-extension pullback is
`m`-regular. -/
@[stacks 08A4] #check (AlgebraicGeometry.ProjectiveSpace.isMRegular_iff_fieldExtension :
  ∀ (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (n : ℕ) (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules)
    [ℱ.IsCoherent] (m : ℤ),
    AlgebraicGeometry.ProjectiveSpace.IsMRegular k n ℱ m ↔
      AlgebraicGeometry.ProjectiveSpace.FieldExtension.IsMRegular k k' n ℱ m)
