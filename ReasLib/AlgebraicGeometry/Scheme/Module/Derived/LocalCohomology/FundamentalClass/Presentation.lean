/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Basis.Morphisms
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.LocalCohomology.FundamentalClass.EquationPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.LocalCohomology

variable {X Z : Scheme.{u}}

/-- A chart for the fundamental class is either an equation chart or an open disjoint from the
closed support. All comparison maps attached to an equation chart are determined internally. -/
inductive Presentation.{v} {X Z : Scheme.{v}} (i : Z ⟶ X) [IsClosedImmersion i]
    (c : ℕ) where
  /-- A chart meeting the support, presented by `c` equations. -/
  | equations (presentation : EquationPresentation i c)
  /-- A chart disjoint from the support. -/
  | away (carrier : X.Opens)
      (disjoint : Disjoint (carrier : Set X) (i.ker.support : Set X))

namespace EquationPresentation

/-- Regard an equation presentation as a chart in the geometric presentation basis. -/
def toPresentation {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : EquationPresentation i c) : Presentation i c :=
  .equations P

end EquationPresentation

namespace Presentation

/-- The ambient open of an equation or off-support chart. -/
def carrier {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ} :
    Presentation i c → X.Opens
  | .equations P => P.carrier
  | .away U _ => U

/-- The local section map on a geometric chart; on an off-support chart it is the canonical zero
map. -/
noncomputable def localMap {i : Z ⟶ X} [IsClosedImmersion i] {c : ℕ}
    (P : Presentation i c) (ℱ : Scheme.QCoh X) :
    ((sourceFunctor i c).obj ℱ).val.presheaf.obj (op P.carrier) ⟶
      ((functor i c).obj ℱ).val.presheaf.obj (op P.carrier) :=
  match P with
  | .equations Q => EquationPresentation.localMap Q ℱ
  | .away _ _ => 0

end Presentation

/-- The induced category of geometric equation charts and off-support charts. Its morphisms are
actual inclusions of ambient opens, not supplied compatibility witnesses. -/
abbrev PresentationCategory (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ) :=
  InducedCategory X.Opens (Presentation.carrier (i := i) (c := c))

/-- Forget a geometric chart to its ambient open. -/
def presentationFunctor (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ) :
    PresentationCategory i c ⥤ X.Opens :=
  inducedFunctor (Presentation.carrier (i := i) (c := c))

/-- Equation charts near the support together with all off-support charts form a topological
basis. The off-support charts are essential for rank `c = 0`. -/
theorem presentations_isBasis (i : Z ⟶ X) (c : ℕ)
    [IsClosedImmersion i] [Scheme.Hom.FinitePresentation i]
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)] :
    Opens.IsBasis (Set.range (Presentation.carrier (i := i) (c := c))) := sorry

/-- Restriction compatibility of the chart maps. For equation charts this is derived from a
genuine change-of-generators matrix and `ModuleCech.LocalCohomology.classMap_mulVec`; if either
chart is off the support it is compatibility of the canonical zero map. -/
theorem Presentation.localMap_naturality (i : Z ⟶ X) (c : ℕ) (ℱ : Scheme.QCoh X)
    [IsClosedImmersion i] {P Q : (PresentationCategory i c)ᵒᵖ} (r : P ⟶ Q) :
    (((presentationFunctor i c).op ⋙
        ((sourceFunctor i c).obj ℱ).val.presheaf).map r) ≫
          Presentation.localMap Q.unop ℱ =
      Presentation.localMap P.unop ℱ ≫
        (((presentationFunctor i c).op ⋙
          ((functor i c).obj ℱ).val.presheaf).map r) := sorry

/-- The additive-presheaf morphism on the geometric presentation basis. -/
noncomputable def localMap (i : Z ⟶ X) (c : ℕ) (ℱ : Scheme.QCoh X)
    [IsClosedImmersion i] :
    (presentationFunctor i c).op ⋙
        ((sourceFunctor i c).obj ℱ).val.presheaf ⟶
      (presentationFunctor i c).op ⋙
        ((functor i c).obj ℱ).val.presheaf where
  app P := Presentation.localMap P.unop ℱ
  naturality _ _ r := Presentation.localMap_naturality i c ℱ r

end AlgebraicGeometry.Scheme.Hom.LocalCohomology

end
