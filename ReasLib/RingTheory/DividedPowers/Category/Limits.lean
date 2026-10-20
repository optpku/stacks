module

public import ReasLib.RingTheory.DividedPowers.Category
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Limits of Divided Power Rings

A limiting cone of commutative rings carries divided powers on the intersection of the
inverse images of the diagram ideals. The divided power operations act coordinatewise.
This construction gives all small limits of divided power rings, and the forgetful functor
preserves limits.
-/

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace DividedPowerRing

namespace forgetCommRing

section

variable {J : Type v} [Category.{w} J] (K : J ⥤ DividedPowerRing.{u})

/-- The ideal of elements whose image lies in the distinguished ideal at every vertex. -/
def coneIdeal (c : Cone (K ⋙ DividedPowerRing.forgetCommRing)) : Ideal c.pt :=
  ⨅ j, (K.obj j).ideal.comap (c.π.app j).hom

@[simp]
theorem mem_coneIdeal (c : Cone (K ⋙ DividedPowerRing.forgetCommRing)) (x : c.pt) :
    x ∈ coneIdeal K c ↔ ∀ j, (c.π.app j).hom x ∈ (K.obj j).ideal := sorry

/-- Divided powers of elements in every coordinate ideal respect the diagram maps. -/
theorem dpowSection_mem (c : Cone (K ⋙ DividedPowerRing.forgetCommRing))
    (n : ℕ) (x : c.pt) (hx : x ∈ coneIdeal K c) :
    (fun j ↦ (K.obj j).dividedPowers.dpow n ((c.π.app j).hom x)) ∈
      ((K ⋙ DividedPowerRing.forgetCommRing) ⋙ forget CommRingCat).sections := sorry

/-- The coordinatewise divided powers of an element of the cone ideal form a compatible
family. -/
def dpowSection (c : Cone (K ⋙ DividedPowerRing.forgetCommRing)) (n : ℕ)
    (x : c.pt) (hx : x ∈ coneIdeal K c) :
    ((K ⋙ DividedPowerRing.forgetCommRing) ⋙ forget CommRingCat).sections :=
  ⟨fun j ↦ (K.obj j).dividedPowers.dpow n ((c.π.app j).hom x),
    dpowSection_mem K c n x hx⟩

@[simp]
theorem dpowSection_apply (c : Cone (K ⋙ DividedPowerRing.forgetCommRing))
    (n : ℕ) (x : c.pt) (hx : x ∈ coneIdeal K c) (j : J) :
    (dpowSection K c n x hx).val j =
      (K.obj j).dividedPowers.dpow n ((c.π.app j).hom x) := rfl

/-- Divided powers on the limiting ring, obtained from coherent coordinate families.
As in `DividedPowers`, the operations are extended by zero off the ideal. -/
noncomputable def limitDividedPowers (c : Cone (K ⋙ DividedPowerRing.forgetCommRing))
    (hc : IsLimit c) : DividedPowers (coneIdeal K c) := by
  classical
  letI : PreservesLimitsOfSize.{w, v} (forget CommRingCat.{u}) :=
    CommRingCat.adj.rightAdjoint_preservesLimits
  exact
    { dpow := fun n x ↦ if hx : x ∈ coneIdeal K c then
        (Types.isLimitEquivSections (isLimitOfPreserves (forget CommRingCat) hc)).symm
          (dpowSection K c n x hx)
        else 0
      dpow_null := by sorry
      dpow_zero := by sorry
      dpow_one := by sorry
      dpow_mem := by sorry
      dpow_add := by sorry
      dpow_mul := by sorry
      mul_dpow := by sorry
      dpow_comp := by sorry }

/-- Each projection of the limiting ring computes divided powers coordinatewise on the ideal. -/
@[simp]
theorem limitDividedPowers_π (c : Cone (K ⋙ DividedPowerRing.forgetCommRing))
    (hc : IsLimit c) (n : ℕ) (x : c.pt) (hx : x ∈ coneIdeal K c) (j : J) :
    (c.π.app j).hom ((limitDividedPowers K c hc).dpow n x) =
      (K.obj j).dividedPowers.dpow n ((c.π.app j).hom x) := sorry

/-- The cone of divided power rings on a specified limiting cone of underlying rings. -/
noncomputable def liftedCone (c : Cone (K ⋙ DividedPowerRing.forgetCommRing))
    (hc : IsLimit c) : Cone K where
  pt := DividedPowerRing.of c.pt (coneIdeal K c) (limitDividedPowers K c hc)
  π :=
    { app := fun j ↦
        { toRingHom := (c.π.app j).hom
          ideal_comp := by sorry
          dpow_comp := by sorry }
      naturality := by sorry }

@[simp]
theorem liftedCone_π_toRingHom (c : Cone (K ⋙ DividedPowerRing.forgetCommRing))
    (hc : IsLimit c) (j : J) :
    ((liftedCone K c hc).π.app j).toRingHom = (c.π.app j).hom := rfl

/-- The universal morphism into the lifted cone is the universal underlying ring morphism. -/
noncomputable def liftedConeIsLimit (c : Cone (K ⋙ DividedPowerRing.forgetCommRing))
    (hc : IsLimit c) : IsLimit (liftedCone K c hc) where
  lift s :=
    { toRingHom := (hc.lift (DividedPowerRing.forgetCommRing.mapCone s)).hom
      ideal_comp := by sorry
      dpow_comp := by sorry }
  fac := by sorry
  uniq := by sorry

@[simp]
theorem liftedConeIsLimit_lift_toRingHom
    (c : Cone (K ⋙ DividedPowerRing.forgetCommRing)) (hc : IsLimit c) (s : Cone K) :
    ((liftedConeIsLimit K c hc).lift s).toRingHom =
      (hc.lift (DividedPowerRing.forgetCommRing.mapCone s)).hom := rfl

/-- Forgetting the chosen lift returns the supplied ring cone by identity maps. -/
noncomputable def liftedConeForgetIso (c : Cone (K ⋙ DividedPowerRing.forgetCommRing))
    (hc : IsLimit c) : DividedPowerRing.forgetCommRing.mapCone (liftedCone K c hc) ≅ c :=
  Cone.ext (Iso.refl c.pt) (by sorry)

/-- The specified limiting ring cone lifted with its coordinatewise divided power structure. -/
noncomputable def liftToLimit (c : Cone (K ⋙ DividedPowerRing.forgetCommRing))
    (hc : IsLimit c) : LiftsToLimit K DividedPowerRing.forgetCommRing c hc where
  liftedCone := liftedCone K c hc
  validLift := liftedConeForgetIso K c hc
  makesLimit := liftedConeIsLimit K c hc

/-- Infrastructure for Lemma 23.3.2 (Tag 07GV): a limiting cone of the underlying commutative-ring
diagram lifts to a limiting cone of divided power rings. -/
@[stacks 07GV "underlying ring of a limit"]
theorem liftsLimit (c : Cone (K ⋙ DividedPowerRing.forgetCommRing)) (hc : IsLimit c) :
    Nonempty (LiftsToLimit K DividedPowerRing.forgetCommRing c hc) :=
  ⟨liftToLimit K c hc⟩

/-- A lifted limiting cone may be bundled as a `LimitCone`; forgetting it recovers the supplied
limiting cone up to canonical isomorphism. -/
theorem liftsLimitCone (c : Cone (K ⋙ DividedPowerRing.forgetCommRing)) (hc : IsLimit c) :
    ∃ c' : LimitCone K,
      Nonempty (DividedPowerRing.forgetCommRing.mapCone c'.cone ≅ c) :=
  ⟨⟨liftedCone K c hc, liftedConeIsLimit K c hc⟩, ⟨liftedConeForgetIso K c hc⟩⟩

/-- A small diagram's limit cone, using the canonical limit of its underlying rings. -/
noncomputable def limitCone [Small.{u} J] : LimitCone K where
  cone := liftedCone K (CommRingCat.limitCone (K ⋙ DividedPowerRing.forgetCommRing))
    (CommRingCat.limitConeIsLimit (K ⋙ DividedPowerRing.forgetCommRing))
  isLimit := liftedConeIsLimit K _ _

/-- Every small diagram of divided power rings admits a limiting cone. -/
theorem existsLimitCone [Small.{u} J] : Nonempty (LimitCone K) :=
  ⟨limitCone K⟩

end

/-- Lemma 23.3.2 (Tag 07GV), part (2): the forgetful functor from divided power rings to
commutative rings preserves all small limits. -/
@[stacks 07GV "underlying ring of a limit"]
instance preservesLimits : PreservesLimits DividedPowerRing.forgetCommRing := sorry

end forgetCommRing

/-- A diagram indexed by a small type has a limit in divided power rings. -/
instance hasLimit {J : Type v} [Category.{w} J] [Small.{u} J]
    (K : J ⥤ DividedPowerRing.{u}) : HasLimit K :=
  HasLimit.mk (forgetCommRing.limitCone K)

/-- Lemma 23.3.2 (Tag 07GV), part (1): the category of divided power rings has all small limits. -/
@[stacks 07GV "all limits"]
instance hasLimits : HasLimits DividedPowerRing.{u} where
  has_limits_of_shape J := { }

end DividedPowerRing
