/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Cartesian
public import ReasLib.AlgebraicGeometry.BivariantClass.OverField

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- The product projections over a field form the cartesian square over its terminal scheme. -/
#check (AlgebraicGeometry.SchemeOverField.productIsPullback :
  {k : Type u} → [Field k] → (X : SchemeOverField k) → {Y : SchemeOverField k} →
    (g : Y ⟶ ⊤_ (SchemeOverField k)) →
      IsPullback ((Limits.prod.fst : X ⨯ Y ⟶ X).left)
        ((Limits.prod.snd : X ⨯ Y ⟶ Y).left) (terminal.from X).left g.left)

/- The field comparison identifies all integer degrees with their negative Chow degree. -/
#check (AlgebraicGeometry.BivariantClass.chowEquiv :
  {k : Type u} → [Field k] → (X : SchemeOverField k) →
    [LocallyOfFiniteType X.hom] → (p : ℤ) →
      @AddEquiv (BivariantClass (fun _ ↦ 0) (terminal.from X) p)
        (RelativeChow (fun _ ↦ 0) X (-p))
        (@AddSemigroup.toAdd _
          (BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0) (terminal.from X) p).toAddCommMonoid.toAddMonoid.toAddSemigroup)
        inferInstance)
