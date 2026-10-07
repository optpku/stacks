module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import stacks_project.Chap109.Lemma_109_21_1_RelativeDualizing

/-!
# Neighbourhood generation of tensor powers of the relative dualizing sheaf

For a prestable family of curves of genus at least one, the fibre over a point
of the base has no rational tail if and only if some neighbourhood of that
point has `dualizingTensorPowerCounit f m` an epimorphism on the inverse
image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.SchemeOverField
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry

/-- If `dualizingTensorPowerCounit f m` is an epimorphism over the inverse image
of some open neighbourhood of `s`, then the fibre over `s` has no rational
tail. -/
theorem no_rational_tail_of_dualizingTensorPower_counit_epi
    {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (s : S)
    (hgenus : 1 ≤ cohomologyFinrank (f.fiberToSpecResidueField s)
        (unit (f.fiber s).ringCatSheaf : (f.fiber s).Modules) 1)
    {m : ℕ} (hm : 2 ≤ m)
    (h : ∃ U : S.Opens, s ∈ U ∧
      Epi ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map
        (dualizingTensorPowerCounit f m))) :
    ¬ Nonempty (RationalTail (Over.mk (f.fiberToSpecResidueField s))) :=
  sorry

/-- If the fibre over `s` has no rational tail, then after shrinking `S` the map
`dualizingTensorPowerCounit f m` is an epimorphism over the inverse image of a
neighbourhood of `s`. -/
theorem dualizingTensorPower_counit_epi_of_no_rational_tail
    {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (s : S)
    (hgenus : 1 ≤ cohomologyFinrank (f.fiberToSpecResidueField s)
        (unit (f.fiber s).ringCatSheaf : (f.fiber s).Modules) 1)
    {m : ℕ} (hm : 2 ≤ m)
    (h : ¬ Nonempty (RationalTail (Over.mk (f.fiberToSpecResidueField s)))) :
    ∃ U : S.Opens, s ∈ U ∧
      Epi ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map
        (dualizingTensorPowerCounit f m)) :=
  sorry

/-- Lemma 109.21.1: for a prestable family of curves `f : X ⟶ S` of genus at
least one, a point `s` of `S`, and `2 ≤ m`, the fibre
`Over.mk (f.fiberToSpecResidueField s)` has no rational tail if and only if
`dualizingTensorPowerCounit f m` is an epimorphism after pullback along
`(f ⁻¹ᵁ U).ι` for some open neighbourhood `U` of `s`. -/
@[stacks 0E6Y]
theorem no_rational_tail_iff_dualizingTensorPower_counit_epi
    {X S : Scheme.{u}} (f : X ⟶ S) [AtWorstNodal f] [IsProper f]
    [(pushforwardCohomologyIn f).IsLeftAdjoint]
    (h_unit : ∀ {S' : Scheme.{u}} (g : S' ⟶ S),
      IsIso (commRingSheafPushforwardMap (pullback.snd f g).toShHom))
    (s : S)
    (hgenus : 1 ≤ cohomologyFinrank (f.fiberToSpecResidueField s)
        (unit (f.fiber s).ringCatSheaf : (f.fiber s).Modules) 1)
    {m : ℕ} (hm : 2 ≤ m) :
    ¬ Nonempty (RationalTail (Over.mk (f.fiberToSpecResidueField s))) ↔
      ∃ U : S.Opens, s ∈ U ∧
        Epi ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map
          (dualizingTensorPowerCounit f m)) :=
  sorry

end AlgebraicGeometry
