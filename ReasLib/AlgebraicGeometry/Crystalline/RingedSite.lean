/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Site
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Base

variable {p : ℕ} [Fact p.Prime] (B : Base.{u} p)

/-- A small crystalline object retains its thickening over the base scheme. -/
def thickeningOverBase :
    smallCrystallineSite B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed ⥤ Over B.scheme where
  obj A := Over.mk A.obj.1.thickeningToBase
  map f := Over.homMk f.hom.thickening f.hom.base_comm
  map_id := sorry
  map_comp := sorry

/-- A big crystalline object retains its thickening over the base scheme. -/
def bigThickeningOverBase :
    RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed ⥤ Over B.scheme where
  obj A := Over.mk A.1.thickeningToBase
  map f := Over.homMk f.thickening f.base_comm
  map_id := sorry
  map_comp := sorry

/-- Lifted functions on small crystalline thickenings form a sheaf for
Zariski covers of thickenings with cartesian source squares. -/
noncomputable def liftedStructureSheaf :
    Sheaf (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers B.compatible
      B.toSpec B.source B.sourceToClosed B.prime_nilpotent) RingCat.{u + 1} :=
  ⟨Presheaf.ringPresheafOfComm
    (Scheme.Over.commStructurePresheaf B.thickeningOverBase), sorry⟩

/-- Lifted functions on big crystalline thickenings form a sheaf for the
crystalline Zariski topology. -/
noncomputable def bigLiftedStructureSheaf :
    Sheaf (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible
      B.source B.sourceToClosed) RingCat.{u + 1} :=
  ⟨Presheaf.ringPresheafOfComm
    (Scheme.Over.commStructurePresheaf B.bigThickeningOverBase), sorry⟩

/-- The small crystalline ringed site carries actual lifted thickening functions. -/
noncomputable abbrev ringedSite : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (smallCrystallineTopology p B.scheme B.ideal B.dividedPowers
    B.compatible B.toSpec B.source B.sourceToClosed B.prime_nilpotent) B.liftedStructureSheaf

/-- The big crystalline ringed site carries actual lifted thickening functions. -/
noncomputable abbrev bigRingedSite : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers
    B.compatible B.source B.sourceToClosed) B.bigLiftedStructureSheaf

/-- Sections of the small crystalline structure sheaf are lifted global
functions on the actual thickening. -/
theorem ringedSite_sections (A : B.ringedSite) :
    B.ringedSite.structureSheaf.obj.obj (op A) =
      RingCat.of (ULift.{u + 1, u} Γ(A.obj.1.thickening, ⊤)) := sorry

/-- Restriction of crystalline functions is pullback along the thickening map. -/
theorem ringedSite_map {A C : B.ringedSite} (f : A ⟶ C)
    (s : B.ringedSite.structureSheaf.obj.obj (op C)) :
    B.ringedSite.structureSheaf.obj.map f.op s =
      ULift.up (f.hom.thickening.appTop.hom s.down) := sorry

end AlgebraicGeometry.Scheme.Crystalline.Base
