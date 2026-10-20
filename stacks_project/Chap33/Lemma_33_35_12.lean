module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity.GlobalGeneration
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 33.35.12: let `k` be a field, let `n ≥ 0`, and let `ℱ` be a coherent sheaf on
projective `n`-space over `k`. If `ℱ` is `m`-regular, then `ℱ(m)` is globally generated. -/
@[stacks 08A8] #check
  (AlgebraicGeometry.ProjectiveSpace.IsMRegular.isGloballyGenerated :
    ∀ {k : Type u} [Field k] {n : ℕ}
      {ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules} [ℱ.IsCoherent] {m : ℤ},
      AlgebraicGeometry.ProjectiveSpace.IsMRegular k n ℱ m →
        SheafOfModules.IsGloballyGenerated
          (AlgebraicGeometry.ProjectiveSpace.twist k n ℱ m))
