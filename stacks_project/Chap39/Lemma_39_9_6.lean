module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.AbelianVariety

/- Lemma 39.9.6: For an invertible module on an abelian variety, there exists an isomorphism
between the tensor product of its pullbacks along the triple sum and the three projections and
the tensor product of its pullbacks along the three pairwise sums. -/
@[stacks 0BFE]
#check (AlgebraicGeometry.AbelianVariety.cubeIso :
  ∀ {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A]
    [AbelianVariety A] (L : A.left.Modules) [Scheme.Modules.Invertible L],
    let T := (A ⊗ A) ⊗ A
    let m₁ : T ⟶ A := fst (A ⊗ A) A ≫ fst A A
    let m₂ : T ⟶ A := fst (A ⊗ A) A ≫ snd A A
    let m₃ : T ⟶ A := snd (A ⊗ A) A
    let m₁₂ := m₁ * m₂
    let m₁₃ := m₁ * m₃
    let m₂₃ := m₂ * m₃
    let m₁₂₃ := m₁₂ * m₃
    let pullbackModule (m : T ⟶ A) := (Scheme.Modules.pullback m.left).obj L
    let lhs :=
      pullbackModule m₁₂₃ ⊗
        (pullbackModule m₁ ⊗ (pullbackModule m₂ ⊗ pullbackModule m₃))
    let rhs :=
      pullbackModule m₁₂ ⊗ (pullbackModule m₁₃ ⊗ pullbackModule m₂₃)
    Nonempty (lhs ≅ rhs))

end AlgebraicGeometry.AbelianVariety
