module

import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BoundednessDetection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure
open RingedSpace.ModuleDerived RingedSpace.Module.Derived
open scoped CartesianClosed DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Proposition 36.40.6: for a perfect weak generator `G` of `D_QCoh(𝒪_X)`, an object
`E` is bounded below if and only if the shifted-Hom, Ext, derived-global-Hom,
dual-tensor hypercohomology, derived-global-sections, and corresponding universal
perfect-object criteria hold. -/
@[stacks 0GEQ] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.boundedBelow_tfae :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (G E : Scheme.ModuleDerived.Quasicoherent X)
      (_ : RingedSpace.ModuleDerived.IsPerfect G.obj) (_ : IsWeakGenerator G),
      ∀ [KFlat.HomotopyTensorDescends X.toRingedSpace]
        [KFlat.TensorDescends X.toRingedSpace]
        [KFlat.IsLocalization X.toRingedSpace]
        [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)],
      List.TFAE
        [ (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj
        , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (G.obj⟦-i⟧ ⟶ E.obj)
        , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(G.obj, E.obj))
        , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((GlobalSections.toAbelian X.toRingedSpace).obj (G.obj ⟹ E.obj))
        , ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
            IsZero ((GlobalSections.cohomologyFunctor X.toRingedSpace i).obj
              (MonoidalClosed.dual G.obj ⊗ E.obj))
        , (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
            ((GlobalSections.toAbelian X.toRingedSpace).obj
              (MonoidalClosed.dual G.obj ⊗ E.obj))
        , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
            RingedSpace.ModuleDerived.IsPerfect P →
              ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (P⟦-i⟧ ⟶ E.obj)
        , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
            RingedSpace.ModuleDerived.IsPerfect P →
              ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))
        , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
            RingedSpace.ModuleDerived.IsPerfect P →
              (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
                ((GlobalSections.toAbelian X.toRingedSpace).obj (P ⟹ E.obj))
        , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
            RingedSpace.ModuleDerived.IsPerfect P →
              ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
                IsZero ((GlobalSections.cohomologyFunctor X.toRingedSpace i).obj
                  (P ⊗ E.obj))
        , ∀ P : RingedSpace.ModuleDerived X.toRingedSpace,
            RingedSpace.ModuleDerived.IsPerfect P →
              (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{u}))
                ((GlobalSections.toAbelian X.toRingedSpace).obj (P ⊗ E.obj))
        ])

end AlgebraicGeometry.Scheme.DerivedQCoh
