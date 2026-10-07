module

public import stacks_project.Chap75.Proposition_75_29_4_BoundednessDetection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry.AlgebraicSpace.Modules
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Proposition 75.29.4: for a quasi-compact quasi-separated algebraic space `X` over a
scheme `S`, a perfect weak generator `G` of `D_QCoh(𝒪_X)`, and `E` in `D_QCoh(𝒪_X)`, the
following are equivalent: `E` is bounded below; shifted Hom from `G` vanishes for `i ≪ 0`;
`Ext⁽i⁾(G, E)` vanishes for `i ≪ 0`; `RHom_X(G, E)` lies in `D⁺(ℤ)`; hypercohomology of
`G^∨ ⊗ E` vanishes for `i ≪ 0`; `RΓ(X, G^∨ ⊗ E)` lies in `D⁺(ℤ)`; and the same Hom, Ext,
global `RHom`, tensor-hypercohomology, and tensor-`RΓ` criteria hold for every perfect
object of `D(𝒪_X)`. -/
@[stacks 0GFI] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.boundedBelow_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (G E : DerivedQCoh X)
      (_ : ModuleDerived.IsPerfect G.obj) (_ : IsWeakGenerator G),
      ∀ [MonoidalCategory (ModuleDerived X)]
        [BraidedCategory (ModuleDerived X)]
        (H : MonoidalClosed (ModuleDerived X)),
      List.TFAE
        [ (t.plus : ObjectProperty (ModuleDerived X)) E.obj
        , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
        , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(G.obj, E.obj))
        , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H G.obj).obj E.obj))
        , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
            IsZero (cohomologyAb X ((ihomOf H G.obj).obj (𝟙_ (ModuleDerived X)) ⊗ E.obj) i)
        , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj
              ((ihomOf H G.obj).obj (𝟙_ (ModuleDerived X)) ⊗ E.obj))
        , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
            ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (P⟦-i⟧ ⟶ E.obj)
        , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
            ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))
        , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
            (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
              ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H P).obj E.obj))
        , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
            ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → IsZero (cohomologyAb X (P ⊗ E.obj) i)
        , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
            (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
              ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ E.obj))
        ])

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
