module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocalHom
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local morphisms of commutative ringed sites

The locality predicate is owned by the bundled morphism of ringed-site presentations.  Its
meaning is locality of the canonical inverse-image structure-sheaf map between independently
sized site categories, so consumers do not carry a separate raw structure map.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uC vC uD vD w

namespace RingedSite.Hom

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable {𝒪C : Sheaf JC CommRingCat.{w}}
variable {𝒪D : Sheaf JD CommRingCat.{w}}

/-- A morphism of commutative ringed-site presentations is local when
its canonical inverse-image structure-sheaf map reflects units objectwise. -/
@[stacks 04HA]
abbrev IsLocal
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪C)
      (RingedSite.ofCommRingSheaf JD 𝒪D))
    [h_adj : (f.base.sheafPushforwardContinuous
      CommRingCat.{w} JD JC).IsRightAdjoint] :
    Prop :=
  CategoryTheory.Sheaf.LocalHom.IsLocal (inverseImageStructureSheafMap f)

/-- The units square of the inverse-image structure-sheaf map is cartesian objectwise. -/
def IsLocal.UnitsSquareCartesian
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪C)
      (RingedSite.ofCommRingSheaf JD 𝒪D))
    [h_adj : (f.base.sheafPushforwardContinuous
      CommRingCat.{w} JD JC).IsRightAdjoint] : Prop :=
  ∀ U : Cᵒᵖ, Units.Square.IsCartesian
    ((inverseImageStructureSheafMap f).hom.app U).hom.toMonoidHom

/-- The bundled locality predicate is exactly locality of the canonical inverse-image
structure-sheaf map. -/
theorem isLocal_iff
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪C)
      (RingedSite.ofCommRingSheaf JD 𝒪D))
    [h_adj : (f.base.sheafPushforwardContinuous
      CommRingCat.{w} JD JC).IsRightAdjoint] :
    f.IsLocal ↔ ∀ U : Cᵒᵖ,
      IsLocalHom ((inverseImageStructureSheafMap f).hom.app U).hom := by
  constructor
  · intro h
    exact h.app
  · intro h
    exact ⟨h⟩

/-- Locality of a bundled ringed-site morphism is
equivalent to objectwise cartesianness of its units square. -/
@[stacks 04HA "units-square criterion"]
theorem isLocal_iff_unitsSquare
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪C)
      (RingedSite.ofCommRingSheaf JD 𝒪D))
    [h_adj : (f.base.sheafPushforwardContinuous
      CommRingCat.{w} JD JC).IsRightAdjoint] :
    f.IsLocal ↔ IsLocal.UnitsSquareCartesian f := by
  simpa only [IsLocal, IsLocal.UnitsSquareCartesian,
    CategoryTheory.Sheaf.LocalHom.UnitsSquareCartesian] using
    (CategoryTheory.Sheaf.LocalHom.unitsSquareCartesian_iff_isLocal
      (inverseImageStructureSheafMap f)).symm

/-- The inverse-image structure map has a cartesian units square. -/
@[stacks 04KR "(1)"]
theorem ofPullback_unitsSquareCartesian
    (F : D ⥤ C) [IsMorphismOfSites JD JC F]
    [(F.sheafPushforwardContinuous
      CommRingCat.{w} JD JC).IsRightAdjoint]
    (𝒪D : Sheaf JD CommRingCat.{w}) :
    IsLocal.UnitsSquareCartesian (ofPullback (JC := JC) F 𝒪D) := sorry

/-- The canonical morphism from an inverse-image presentation is
local. -/
@[stacks 04KR "(2)"]
instance ofPullback_isLocal
    (F : D ⥤ C) [IsMorphismOfSites JD JC F]
    [(F.sheafPushforwardContinuous
      CommRingCat.{w} JD JC).IsRightAdjoint]
    (𝒪D : Sheaf JD CommRingCat.{w}) :
    CategoryTheory.Sheaf.LocalHom.IsLocal
      (inverseImageStructureSheafMap (ofPullback (JC := JC) F 𝒪D)) :=
  (isLocal_iff_unitsSquare (ofPullback (JC := JC) F 𝒪D)).mpr
    (ofPullback_unitsSquareCartesian (JC := JC) F 𝒪D)

end RingedSite.Hom
