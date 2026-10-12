/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Truncation
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
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.DerivedQCoh.homSubsingletonEventually_iff_truncGE :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      {P : AlgebraicGeometry.AlgebraicSpace.SmallEtale.ModuleDerived X},
      AlgebraicGeometry.AlgebraicSpace.SmallEtale.ModuleDerived.IsPerfect P →
        ∀ (E : AlgebraicGeometry.AlgebraicSpace.SmallEtale.DerivedQCoh X) (a : ℤ),
          (∀ᶠ i : ℤ in Filter.atTop,
            Subsingleton (P⟦-i⟧ ⟶ E.obj)) ↔
          ∀ᶠ i : ℤ in Filter.atTop,
            Subsingleton (P⟦-i⟧ ⟶ (t.truncGE a).obj E.obj))

#check
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.DerivedQCoh.extSubsingletonEventually_iff_truncGE :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      {P : AlgebraicGeometry.AlgebraicSpace.SmallEtale.ModuleDerived X},
      AlgebraicGeometry.AlgebraicSpace.SmallEtale.ModuleDerived.IsPerfect P →
        ∀ (E : AlgebraicGeometry.AlgebraicSpace.SmallEtale.DerivedQCoh X) (a : ℤ),
          (∀ᶠ i : ℤ in Filter.atTop,
            Subsingleton (Ext⁽i⁾(P, E.obj))) ↔
          ∀ᶠ i : ℤ in Filter.atTop,
            Subsingleton (Ext⁽i⁾(P, (t.truncGE a).obj E.obj)))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
