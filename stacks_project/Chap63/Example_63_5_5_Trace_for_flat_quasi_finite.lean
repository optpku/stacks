/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap63.Example_63_5_5_Trace_for_flat_quasi_finite_Comparison
public import stacks_project.Chap63.Example_63_5_5_Trace_for_flat_quasi_finite_Trace
import StacksCheckRecall

/-!
# Trace for flat quasi-finite morphisms

Example 63.5.5: a flat, locally quasi-finite, locally finitely presented
scheme morphism has a canonical positive fibre-weight weighting, hence
canonical derived traces `Tr_{f, K}` compatible with base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Example 63.5.5 (Trace for flat quasi-finite) (1): Let `f : X ⟶ Y` be a
morphism of schemes which is flat, locally quasi-finite, and locally of finite
presentation. The canonical positive weighting is `f.fiberWeight`, with
`f.fiberWeight x` equal to the length of the local closed fibre at `x` times
the finite inseparable degree of `κ(x)` over `κ(f x)`. -/
@[stacks 0GKI] #check
  (fiberWeight_apply :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
      f.fiberWeight x =
        ((Module.length (X.presheaf.stalk x)
              ((X.presheaf.stalk x) ⧸
                (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map
                  (f.stalkMap x).hom)).toNat *
            Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) : ℕ))

@[stacks 0GKI] #check
  (fiberWeight_isPositiveWeighting :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f],
      f.IsWeighting f.fiberWeight ∧ ∀ x : X, 0 < f.fiberWeight x)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f).op]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Example 63.5.5 (Trace for flat quasi-finite) (2): Let `f : X ⟶ Y` be a
flat, locally quasi-finite, locally finitely presented morphism of schemes.
Lemmas 63.5.2 and 63.5.3 supply canonical derived traces
`Tr_{f, K} : f_! f⁻¹ K ⟶ K` on `D(Y_étale, Λ)`. -/
@[stacks 0GKI]
def fiberWeightTraceDerived (K : EtaleDerived Y Λ) :
    (lowerShriekModuleDerived f Λ).obj
        ((etaleModuleDerivedInverseImage f Λ).obj K) ⟶ K :=
  fiberWeightTraceDerivedHom f Λ K

/-- The source-facing derived fibre-weight trace is
`fiberWeightTraceDerivedHom`. -/
theorem fiberWeightTraceDerived_eq (K : EtaleDerived Y Λ) :
    fiberWeightTraceDerived f Λ K = fiberWeightTraceDerivedHom f Λ K :=
  sorry

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.Hom

/- Example 63.5.5 (Trace for flat quasi-finite) (3): Any cartesian base change
`f' : X' ⟶ Y'` of `f` is again flat, locally quasi-finite, and locally of
finite presentation, and `f.fiberWeight` restricts to the canonical weighting
`f'.fiberWeight`. -/
@[stacks 0GKI] #check
  (fiberWeight_isPullback :
    ∀ {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
      (f' : X' ⟶ Y') (g' : X' ⟶ X)
      [Flat f] [LocallyQuasiFinite f] [LocallyOfFinitePresentation f]
      [Flat f'] [LocallyQuasiFinite f'] [LocallyOfFinitePresentation f'],
      IsPullback g' f' f g →
        (fun x' : X' ↦ f.fiberWeight (g' x')) = f'.fiberWeight)

end AlgebraicGeometry.Scheme.Hom

end
