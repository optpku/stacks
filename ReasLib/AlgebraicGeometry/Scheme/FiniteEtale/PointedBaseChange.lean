/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Galois.GaloisObjects
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- A finite étale Galois cover is split over a rational point when that point has a
rational lift to the cover. -/
def IsSplitOver {k : Type u} [Field k] {X : Scheme.{u}}
    [GaloisCategory (Scheme.FiniteEtale X)]
    (Z : Scheme.FiniteEtale X) [IsGalois Z]
    (p : Spec (CommRingCat.of k) ⟶ X) : Prop :=
  ∃ s : Spec (CommRingCat.of k) ⟶ Z.left, s ≫ Z.hom = p

/-- Splitting of a finite étale Galois cover over a rational point is equivalent to the
existence of a rational lift of that point. -/
theorem IsSplitOver.iff {k : Type u} [Field k] {X : Scheme.{u}}
    [GaloisCategory (Scheme.FiniteEtale X)]
    (Z : Scheme.FiniteEtale X) [IsGalois Z]
    (p : Spec (CommRingCat.of k) ⟶ X) :
    IsSplitOver Z p ↔ ∃ s : Spec (CommRingCat.of k) ⟶ Z.left, s ≫ Z.hom = p :=
  Iff.rfl

/-- The comparison morphism `Z_{K'} ⟶ X_K` induced by a finite étale cover of `X_{k'}`
after extending scalars along `k' ⊂ K'` and `K ⊂ K'`. -/
noncomputable def toBaseChange
    {k k' : Type u} (K K' : Type u)
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k' K'] [Algebra K K']
    [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    (X : SchemeOverField k)
    (Z : Scheme.FiniteEtale (FieldExtension.Over.baseChange k k' X).left) :
    FieldExtension.baseChange k' K'
        (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ⟶
      (FieldExtension.Over.baseChange k K X).left :=
  pullback.lift
    (FieldExtension.toSource k' K'
        (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
      Z.hom ≫ FieldExtension.toSource k k' X.hom)
    (FieldExtension.toBase k' K'
        (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
      FieldExtension.specMap K K')
    (by
      calc
        _ = FieldExtension.toSource k' K'
                (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
              Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom ≫
                FieldExtension.specMap k k' := by
          simp only [Category.assoc]
          exact congrArg
            (fun f => FieldExtension.toSource k' K'
                (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫ Z.hom ≫ f)
            (pullback.condition (f := X.hom) (g := FieldExtension.specMap k k'))
        _ = (FieldExtension.toSource k' K'
                (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
              (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom)) ≫
                FieldExtension.specMap k k' := by
          simp only [Category.assoc]
        _ = (FieldExtension.toBase k' K'
                (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
              FieldExtension.specMap k' K') ≫ FieldExtension.specMap k k' := by
          rw [pullback.condition]
        _ = _ := by
          simp only [Category.assoc, FieldExtension.specMap,
            Scheme.AffineBaseChange.specMap_comp])

/-- The comparison `Z_{K'} ⟶ X_K` projects to `X` as the composite through `Z` and `X_{k'}`. -/
theorem toBaseChange_comp_toSource
    {k k' : Type u} (K K' : Type u)
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k' K'] [Algebra K K']
    [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    (X : SchemeOverField k)
    (Z : Scheme.FiniteEtale (FieldExtension.Over.baseChange k k' X).left) :
    toBaseChange K K' X Z ≫ FieldExtension.toSource k K X.hom =
      FieldExtension.toSource k' K'
          (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
        Z.hom ≫ FieldExtension.toSource k k' X.hom :=
  sorry

/-- The comparison `Z_{K'} ⟶ X_K` projects to `Spec K` as `Z_{K'} ⟶ Spec K' ⟶ Spec K`. -/
theorem toBaseChange_comp_toBase
    {k k' : Type u} (K K' : Type u)
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k' K'] [Algebra K K']
    [Algebra k K'] [IsScalarTower k k' K'] [IsScalarTower k K K']
    (X : SchemeOverField k)
    (Z : Scheme.FiniteEtale (FieldExtension.Over.baseChange k k' X).left) :
    toBaseChange K K' X Z ≫ FieldExtension.toBase k K X.hom =
      FieldExtension.toBase k' K'
          (Z.hom ≫ (FieldExtension.Over.baseChange k k' X).hom) ≫
        FieldExtension.specMap K K' :=
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
