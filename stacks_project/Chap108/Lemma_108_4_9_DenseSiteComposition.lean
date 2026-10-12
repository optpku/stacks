/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]

/-- Cover density composes when the outer functor preserves covering sieves. -/
theorem coverDense_comp (G : A ⥤ B) (F : B ⥤ C)
    (J : GrothendieckTopology B) (K : GrothendieckTopology C)
    [G.IsCoverDense J] [F.IsCoverDense K] (hF : CoverPreserving J K F) :
    (G ⋙ F).IsCoverDense K where
  is_cover X := by
    apply K.transitive (F.is_cover_of_isCoverDense K X)
    rintro W k ⟨⟨Y, a, b, fac⟩⟩
    have hcover := hF.cover_preserve (G.is_cover_of_isCoverDense J Y)
    have hle : (Sieve.coverByImage G Y).functorPushforward F ≤
        (Sieve.coverByImage (G ⋙ F) X).pullback b := by
      rintro Z t ⟨Y', i, r, ⟨⟨d, p, q, hpq⟩⟩, ht⟩
      refine ⟨⟨d, r ≫ F.map p, F.map q ≫ b, ?_⟩⟩
      calc
        (r ≫ F.map p) ≫ (F.map q ≫ b) = (r ≫ F.map (p ≫ q)) ≫ b := by
          simp only [CategoryTheory.Functor.map_comp, Category.assoc]
        _ = (r ≫ F.map i) ≫ b := by rw [hpq]
        _ = t ≫ b := by rw [ht]
    have hb := K.superset_covering hle hcover
    rw [← fac, Sieve.pullback_comp]
    exact K.pullback_stable a hb

/-- Replacing the source of a cover-dense functor by an equivalent category preserves density. -/
theorem coverDense_precomp_equivalence (e : A ≌ B) (F : B ⥤ C)
    (K : GrothendieckTopology C) [F.IsCoverDense K] :
    (e.functor ⋙ F).IsCoverDense K where
  is_cover X := by
    apply K.superset_covering _ (F.is_cover_of_isCoverDense K X)
    rintro Y f ⟨⟨Z, a, b, hab⟩⟩
    let iso := F.mapIso (e.counitIso.app Z)
    refine ⟨⟨e.inverse.obj Z, a ≫ iso.inv, iso.hom ≫ b, ?_⟩⟩
    calc
      (a ≫ iso.inv) ≫ (iso.hom ≫ b) = a ≫ (iso.inv ≫ iso.hom ≫ b) := Category.assoc _ _ _
      _ = a ≫ b := congrArg (fun k ↦ a ≫ k) (iso.inv_hom_id_assoc b)
      _ = f := hab

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
