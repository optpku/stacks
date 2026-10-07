module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedRing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ModuleRestrictionIso
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteFreeModuleResolution

@[expose] public section
open CategoryTheory
noncomputable section
universe u v

namespace NoncommGroupAlgebraModule
variable (R : Type u) [Ring R]
variable (G : Type v) [Group G]

/-- The representation carrier with its new group-algebra action. -/
def Carrier (M : Action (ModuleCat.{max u v} R) G) := M.V

instance carrier_addCommGroup (M : Action (ModuleCat.{max u v} R) G) : AddCommGroup (Carrier R G M) :=
  inferInstanceAs (AddCommGroup M.V)

/-- Finite group-algebra sums act by LEFT coefficients and the specified group action. -/
def scalar (M : Action (ModuleCat.{max u v} R) G) (r : MonoidAlgebra R G) (m : Carrier R G M) :
    Carrier R G M := r.coeff.sum (fun g a ↦ a • (M.ρ g).hom m)

/-- This is an action by additive endomorphisms, without any CommRing premise. -/
instance groupAlgebraModule (M : Action (ModuleCat.{max u v} R) G) :
    Module (MonoidAlgebra R G) (Carrier R G M) where
  smul := scalar R G M
  one_smul := by sorry
  mul_smul := by sorry
  smul_zero := by sorry
  smul_add := by sorry
  zero_smul := by sorry
  add_smul := by sorry

/-- Bundle exactly that action. -/
def module (M : Action (ModuleCat.{max u v} R) G) : ModuleCat.{max u v} (MonoidAlgebra R G) :=
  ModuleCat.of (MonoidAlgebra R G) (Carrier R G M)

/-- Equivariant R-linear maps are linear for the actual group-algebra sum action. -/
def toFunctor : Action (ModuleCat.{max u v} R) G ⥤ ModuleCat.{max u v} (MonoidAlgebra R G) where
  obj := module R G
  map f := ModuleCat.ofHom
    { toFun := fun x ↦ f.hom.hom x
      map_add' := f.hom.hom.map_add
      map_smul' := by sorry }
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The actual noncommutative coefficient inclusion. -/
abbrev scalarHom : R →+* MonoidAlgebra R G := MonoidAlgebra.singleOneRingHom

/-- Group basis elements commute with the coefficient subring, so this
particular action is R-linear; general group-algebra elements need not be. -/
def groupLinear (M : ModuleCat.{max u v} (MonoidAlgebra R G)) (g : G) :
    (ModuleCat.restrictScalars (scalarHom R G)).obj M →ₗ[R]
      (ModuleCat.restrictScalars (scalarHom R G)).obj M :=
  -- Local instance justification (defeq pin): expose the actual scalar inclusion on this module carrier.
  letI := Module.compHom M (scalarHom R G)
  { toFun := fun x ↦ MonoidAlgebra.single g (1 : R) • (show M from x)
    map_add' := by intros; exact smul_add _ _ _
    map_smul' := by sorry }

/-- Recover the original coefficient and group actions from actual scalars and Dirac elements. -/
def fromFunctor : ModuleCat.{max u v} (MonoidAlgebra R G) ⥤ Action (ModuleCat.{max u v} R) G where
  obj M :=
    -- Local instance justification (defeq pin): the recovered group maps use this same coefficient restriction.
    letI := Module.compHom M (scalarHom R G)
    { V := (ModuleCat.restrictScalars (scalarHom R G)).obj M
      ρ := { toFun := fun g ↦ ModuleCat.ofHom (groupLinear R G M g)
             map_one' := by sorry
             map_mul' := by sorry } }
  map f := { hom := (ModuleCat.restrictScalars (scalarHom R G)).map f
             comm := fun _ ↦ by sorry }
  map_id := by intros; rfl
  map_comp := by intros; rfl

instance fromFunctor_additive : (fromFunctor R G).Additive := by sorry
instance fromFunctor_preservesHomology : (fromFunctor R G).PreservesHomology := by sorry

/-- Identity on vectors identifies recovered actions with the given representation. -/
def actionIso (M : Action (ModuleCat.{max u v} R) G) :
    (fromFunctor R G).obj ((toFunctor R G).obj M) ≅ M :=
  Action.mkIso
    (ActualModuleRestriction.restrictionIso (scalarHom R G) (module R G M) M.V
      (AddEquiv.refl _) (by sorry)) (fun _ ↦ by sorry)

/-- Finiteness of a group algebra is used only for a genuinely finite group. -/
theorem ring_finite [Finite R] [Finite G] : Finite (MonoidAlgebra R G) :=
  Finite.of_injective (fun x : MonoidAlgebra R G ↦ (x.coeff : G → R))
    (DFunLike.coe_injective.comp MonoidAlgebra.coeff_injective)

/-- The bundled group-algebra carrier is still the original finite set. -/
theorem module_finite (M : Action (ModuleCat.{max u v} R) G) [Finite M.V] :
    Finite (module R G M) := inferInstanceAs (Finite M.V)

end NoncommGroupAlgebraModule
