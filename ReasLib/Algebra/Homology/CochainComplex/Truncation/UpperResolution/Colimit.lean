/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import ReasLib.Algebra.Homology.HomologicalComplex.Colimit
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.UpperResolution

/-!
# Colimits of Upper-Truncation Resolution Towers

This leaf proves the property-neutral stabilization statements for an upper-
truncation resolution and exposes two interfaces for recognizing its colimit
comparison as a quasi-isomorphism.  No sheaf, module, or ringed-site model is
fixed here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex.UpperTruncation.Resolution

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {P : ObjectProperty A} {K : CochainComplex A ℤ}

/-- Once the cutoff contains degree `i`, the stage-to-target map is a
quasi-isomorphism at `i`. -/
theorem toTarget_quasiIsoAt_of_le_index
    (S : UpperTruncation.Resolution P K) (i : ℤ) {n : ℕ}
    (h : i ≤ UpperTruncation.index n) : QuasiIsoAt (S.toTarget n) i := sorry

/-- Once a cutoff contains degree `i`, the induced diagram on `i`th homology
is eventually constant from that stage. -/
theorem homologyDiagram_isEventuallyConstantFrom_of_le_index
    (S : UpperTruncation.Resolution P K) (i : ℤ) {n : ℕ}
    (h : i ≤ UpperTruncation.index n) :
    Functor.IsEventuallyConstantFrom
      (S.tower ⋙ HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i) n := sorry

/-- The canonical leg at `stageForDegree i` of the mapped homology cocone is
an isomorphism. -/
noncomputable instance toTarget_homologyCocone_leg_isIso
    (S : UpperTruncation.Resolution P K) (i : ℤ) :
    IsIso (((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i).mapCocone
      S.cocone).ι.app (UpperTruncation.stageForDegree i)) := sorry

/-- The legs of the target cocone after applying homology are the maps on
homology induced by the stage-to-target morphisms. -/
@[simp]
theorem toTargetHomologyCocone_ι_app
    (S : UpperTruncation.Resolution P K) (i : ℤ) (n : ℕ) :
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i).mapCocone
      S.cocone).ι.app n = HomologicalComplex.homologyMap (S.toTarget n) i := sorry

/-- For every degree, applying homology to the target cocone yields a colimit
cocone because the tower is eventually constant in that degree. -/
noncomputable def toTargetHomologyCoconeIsColimit
    (S : UpperTruncation.Resolution P K) (i : ℤ) :
    IsColimit
      ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i).mapCocone S.cocone) :=
  (homologyDiagram_isEventuallyConstantFrom_of_le_index S i
    (UpperTruncation.le_index_stageForDegree i)).isColimitOfIsIso _

/-- If degreewise homology-colimit comparisons for this resolving tower have
the canonical formula on every colimit inclusion, then the map from its
colimit to the target complex is a quasi-isomorphism. -/
theorem fromColimit_quasiIso_of_colimitHomologyIso
    (S : UpperTruncation.Resolution P K) [HasColimit S.tower]
    [∀ i : ℤ, HasColimit
      (S.tower ⋙ HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i)]
    (colimitHomologyIso : ∀ i : ℤ,
      colimit (S.tower ⋙ HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i) ≅
        (colimit S.tower).homology i)
    (colimitHomologyIso_hom_ι : ∀ (i : ℤ) (n : ℕ),
        colimit.ι
            (S.tower ⋙ HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i) n ≫
            (colimitHomologyIso i).hom =
          HomologicalComplex.homologyMap (colimit.ι S.tower n) i) :
    QuasiIso S.fromColimit := sorry

/-- If every homology functor preserves the colimit of the resolving tower,
then the canonical map from that colimit to the target is a quasi-isomorphism.
-/
theorem fromColimit_quasiIso_of_preservesColimit
    (S : UpperTruncation.Resolution P K) [HasColimit S.tower]
    [∀ i : ℤ, PreservesColimit S.tower
      (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i)] :
    QuasiIso S.fromColimit := sorry

section

variable [HasColimitsOfShape ℕ A]

/-- Exact sequential colimits make the canonical map from an upper-resolution
colimit to its target a quasi-isomorphism. -/
theorem fromColimit_quasiIso_of_exactColimits
    [HasExactColimitsOfShape ℕ A] (S : UpperTruncation.Resolution P K) :
    QuasiIso S.fromColimit := sorry

attribute [instance] fromColimit_quasiIso_of_exactColimits

/-- Under the standard object-property hypotheses and exact sequential
colimits, there exists an upper-truncation resolution whose canonical colimit
map is a quasi-isomorphism. -/
theorem exists_with_quasiIso_fromColimit
    (P : ObjectProperty A) [P.ContainsZero]
    [P.IsClosedUnderFiniteCoproducts] [P.HasEpiCover]
    [HasExactColimitsOfShape ℕ A] (K : CochainComplex A ℤ) :
    ∃ S : UpperTruncation.Resolution P K, QuasiIso S.fromColimit := sorry

end

end CochainComplex.UpperTruncation.Resolution
