/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Stratification
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Constructible

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A quasi-finite finitely presented morphism between affine schemes admits a
surjective affine base change containing a thickening finite etale over the new base. -/
theorem exists_surjective_affine_baseChange_finiteEtale_thickening
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] [IsAffine Y]
    [QuasiFinite f] [FinitePresentation f] :
    ∃ (X' Z' : Scheme.{u}) (g : X' ⟶ X) (i : Z' ⟶ pullback g f),
      IsAffine X' ∧ Surjective g ∧ IsThickening i ∧
        IsFinite (i ≫ pullback.fst g f) ∧ Etale (i ≫ pullback.fst g f) := sorry

/-- A quasi-finite finitely presented morphism between affine schemes admits a
finite affine constructible stratification with finite locally free covers whose
reduced base changes split as finite coproducts of reduced bases. -/
theorem exists_finiteAffineStratification_reduction_iso_coproduct
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffine X] [IsAffine Y]
    [QuasiFinite f] [FinitePresentation f] :
    ∃ (S : Scheme.Stratification X) (_ : Finite S.index)
      (_ : ∀ i, Topology.IsConstructible (Set.range (S.ι i).base))
      (_ : ∀ i, IsAffine (S.stratum i))
      (X' : S.index → Scheme.{u}) (g : ∀ i, X' i ⟶ S.stratum i)
      (_ : ∀ i, Surjective (g i))
      (_ : ∀ i, IsFiniteLocallyFree (g i)) (n : S.index → ℕ)
      (e : ∀ i, Scheme.reduction (pullback (g i ≫ S.ι i) f) ≅
        ∐ fun _ : Fin (n i) ↦ Scheme.reduction (X' i)),
      ∀ i, Scheme.reductionMap (pullback.fst (g i ≫ S.ι i) f) =
        (e i).hom ≫ Sigma.desc (fun _ : Fin (n i) ↦ 𝟙 (Scheme.reduction (X' i))) := sorry

end AlgebraicGeometry.Scheme.Hom
