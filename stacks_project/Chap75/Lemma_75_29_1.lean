module

public import stacks_project.Chap75.Lemma_75_29_1_Truncation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.29.1: on a quasi-compact quasi-separated algebraic space `X` over a scheme `S`,
for `P` perfect in `D(𝒪_X)`, `E` in `D_QCoh(𝒪_X)`, and `a : ℤ`, eventual vanishing of
`Hom(P⟦-i⟧, E)` in `D(𝒪_X)` for `i ≫ 0` is equivalent to the same vanishing after replacing
`E` by `(t.truncGE a).obj E`. -/
@[stacks 0GFF] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.homSubsingletonEventually_iff_truncGE :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      {P : ModuleDerived X},
      ModuleDerived.IsPerfect P →
        ∀ (E : DerivedQCoh X) (a : ℤ),
          (∀ᶠ i : ℤ in Filter.atTop,
            Subsingleton (P⟦-i⟧ ⟶ (inclusion X).obj E)) ↔
          ∀ᶠ i : ℤ in Filter.atTop,
            Subsingleton (P⟦-i⟧ ⟶ (t.truncGE a).obj ((inclusion X).obj E)))

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.extSubsingletonEventually_iff_truncGE :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      {P : ModuleDerived X},
      ModuleDerived.IsPerfect P →
        ∀ (E : DerivedQCoh X) (a : ℤ),
          (∀ᶠ i : ℤ in Filter.atTop,
            Subsingleton (Ext⁽i⁾(P, (inclusion X).obj E))) ↔
          ∀ᶠ i : ℤ in Filter.atTop,
            Subsingleton (Ext⁽i⁾(P, (t.truncGE a).obj ((inclusion X).obj E))))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
