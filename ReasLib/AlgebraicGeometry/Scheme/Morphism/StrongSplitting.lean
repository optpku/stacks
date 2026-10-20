module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Fiber

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The common point-set fibre of two parallel scheme morphisms over a target point. -/
def commonFiberPoints {X U : Scheme.{u}} (source target : X ⟶ U) (point : U) : Set X :=
  source ⁻¹' ({point} : Set U) ∩ target ⁻¹' ({point} : Set U)

/-- Two parallel scheme morphisms satisfy strong-splitting hypotheses at a target point when
both are separated and locally of finite type, their common point-set fibre is finite, and
the source is finite-type quasi-finite at every point of that common fibre. -/
class StrongSplittingAt {X U : Scheme.{u}} (source target : X ⟶ U) (point : U) : Prop where
  /-- The source morphism is separated. -/
  [source_isSeparated : IsSeparated source]
  /-- The target morphism is separated. -/
  [target_isSeparated : IsSeparated target]
  /-- The source morphism is locally of finite type. -/
  [source_locallyOfFiniteType : LocallyOfFiniteType source]
  /-- The target morphism is locally of finite type. -/
  [target_locallyOfFiniteType : LocallyOfFiniteType target]
  /-- The common point-set fibre at the chosen target point is finite. -/
  finite_commonFiberPoints : (commonFiberPoints source target point).Finite
  /-- The source is finite-type quasi-finite at every point of the common fibre. -/
  source_quasiFiniteAt_commonFiberPoints :
    ∀ arrow ∈ commonFiberPoints source target point, FiniteType.QuasiFiniteAt source arrow

attribute [instance] StrongSplittingAt.source_isSeparated StrongSplittingAt.target_isSeparated
  StrongSplittingAt.source_locallyOfFiniteType StrongSplittingAt.target_locallyOfFiniteType

namespace StrongSplittingAt

/-- Separated, locally finite type parallel morphisms with finite common point-set fibre and
source finite-type quasi-finiteness on that fibre satisfy strong-splitting hypotheses. -/
theorem of {X U : Scheme.{u}} (source target : X ⟶ U) (point : U)
    [IsSeparated source] [IsSeparated target]
    [LocallyOfFiniteType source] [LocallyOfFiniteType target]
    (hfin : (commonFiberPoints source target point).Finite)
    (hqf : ∀ arrow ∈ commonFiberPoints source target point,
      FiniteType.QuasiFiniteAt source arrow) :
    StrongSplittingAt source target point where
  finite_commonFiberPoints := hfin
  source_quasiFiniteAt_commonFiberPoints := hqf

/-- Strong-splitting hypotheses are equivalent to separatedness and local finite type of both
morphisms, finiteness of the common point-set fibre, and source finite-type quasi-finiteness
at every member of that fibre. -/
theorem iff {X U : Scheme.{u}} (source target : X ⟶ U) (point : U) :
    StrongSplittingAt source target point ↔
      IsSeparated source ∧ IsSeparated target ∧
        LocallyOfFiniteType source ∧ LocallyOfFiniteType target ∧
          (commonFiberPoints source target point).Finite ∧
            ∀ arrow ∈ commonFiberPoints source target point,
              FiniteType.QuasiFiniteAt source arrow := sorry

/-- For separated, locally finite type parallel morphisms, a finite source point-set fibre
implies strong-splitting hypotheses at the chosen target point. -/
theorem ofFiniteSourceFiber {X U : Scheme.{u}} (source target : X ⟶ U) (point : U)
    [IsSeparated source] [IsSeparated target]
    [LocallyOfFiniteType source] [LocallyOfFiniteType target]
    (hfin : Set.Finite (source ⁻¹' ({point} : Set U))) :
    StrongSplittingAt source target point := sorry

/-- A finite source point-set fibre supplies strong-splitting hypotheses when both parallel
morphisms are separated and locally of finite type. -/
instance instOfFiniteSourceFiber {X U : Scheme.{u}} (source target : X ⟶ U) (point : U)
    [hfin : Fact (Set.Finite (source ⁻¹' ({point} : Set U)))]
    [IsSeparated source] [IsSeparated target]
    [LocallyOfFiniteType source] [LocallyOfFiniteType target] :
    StrongSplittingAt source target point :=
  StrongSplittingAt.ofFiniteSourceFiber source target point hfin.out

end StrongSplittingAt

end AlgebraicGeometry.Scheme.Hom
