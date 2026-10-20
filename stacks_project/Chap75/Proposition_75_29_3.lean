module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BoundednessDetection

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure
open scoped DerivedExt CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Proposition 75.29.3: on a quasi-compact quasi-separated algebraic space `X` over a
scheme `S`, for a perfect weak generator `G` of `D_QCoh(𝒪_X)` and `E` in `D_QCoh(𝒪_X)`,
bounded-above membership of `E` is equivalent to eventual vanishing of
`Hom(G⟦-i⟧, E)` and `Ext⁽i⁾(G, E)`, to `RHom_X(G, E)` and `RΓ(X, G^∨ ⊗ E)` lying in
`D^-(Z)`, to eventual vanishing of `H^i(X, G^∨ ⊗ E)`, and to the same Hom/Ext/RHom
criteria together with underived-dual-free tensor hypercohomology for every perfect
object of `D(𝒪_X)`. Source items (1)–(6) are TFAE indices 0–5; source (7) flattens to
indices 6–10 as Hom, Ext, RHom, tensor cohomology, and tensor RΓ. -/
@[stacks 0GFH] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.boundedAbove_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [MonoidalCategory (ModuleDerived X)] [BraidedCategory (ModuleDerived X)]
      (H : MonoidalClosed (ModuleDerived X))
      (M : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := Modules X))
      (G E : DerivedQCoh X)
      (_ : ModuleDerived.IsPerfect G.obj) (_ : IsWeakGenerator G),
      List.TFAE
        [ (t.minus : ObjectProperty (ModuleDerived X)) E.obj
        , ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
        , ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(G.obj, E.obj))
        , (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H G.obj).obj E.obj))
        , ∀ᶠ i : ℤ in Filter.atTop,
            IsZero (cohomologyAb X ((ihomOf H G.obj).obj ((DerivedCategory.singleFunctor (Modules X) 0).obj (𝟙_ (Modules X))) ⊗ᴸ E.obj) i)
        , (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((moduleDerivedGlobalSectionsAb X).obj
              ((ihomOf H G.obj).obj ((DerivedCategory.singleFunctor (Modules X) 0).obj (𝟙_ (Modules X))) ⊗ᴸ E.obj))
        , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
            ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (P⟦-i⟧ ⟶ E.obj)
        , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
            ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(P, E.obj))
        , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
            (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
              ((moduleDerivedGlobalSectionsAb X).obj ((ihomOf H P).obj E.obj))
        , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
            ∀ᶠ i : ℤ in Filter.atTop, IsZero (cohomologyAb X (P ⊗ᴸ E.obj) i)
        , ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
            (t.minus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
              ((moduleDerivedGlobalSectionsAb X).obj (P ⊗ᴸ E.obj))
        ])

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.boundedAbove_iff_extEventually :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (G E : DerivedQCoh X)
      (_ : ModuleDerived.IsPerfect G.obj) (_ : IsWeakGenerator G),
      (t.minus : ObjectProperty (ModuleDerived X)) E.obj ↔
        ∀ᶠ i : ℤ in Filter.atTop, Subsingleton (Ext⁽i⁾(G.obj, E.obj)))

#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.boundedAbove_iff_perfectTensorCohomologyEventually :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (E : DerivedQCoh X),
      (t.minus : ObjectProperty (ModuleDerived X)) E.obj ↔
        ∀ P : ModuleDerived X, ModuleDerived.IsPerfect P →
          ∀ᶠ i : ℤ in Filter.atTop, IsZero (cohomologyAb X (P ⊗ᴸ E.obj) i))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
