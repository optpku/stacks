module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The first exterior power

The canonical isomorphism `Λ¹(M) ≅ M` is exposed in the inverse direction as the degree-one
generator map. This direction composes directly with homogeneous inclusions into total objects.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace ModuleCat.exteriorPower

variable {R : Type u} [CommRing R]

/-- The canonical isomorphism from a module to its first exterior power. -/
@[stacks 01CF "module as its first exterior power"]
noncomputable def degreeOneIso (M : ModuleCat.{max u v} R) :
    M ≅ M.exteriorPower 1 :=
  (_root_.exteriorPower.oneEquiv R M).toModuleIso.symm

/-- The canonical map from a module to its first exterior power. -/
noncomputable def degreeOne (M : ModuleCat.{max u v} R) :
    M ⟶ M.exteriorPower 1 :=
  (degreeOneIso M).hom

/-- The inverse first-exterior-power isomorphism evaluates by `exteriorPower.oneEquiv`. -/
@[simp, stacks 01CF "inverse first exterior power evaluation"]
theorem degreeOneIso_inv_apply (M : ModuleCat.{max u v} R)
    (x : M.exteriorPower 1) :
    (degreeOneIso M).inv x = _root_.exteriorPower.oneEquiv R M x := sorry

/-- The degree-one maps are natural in the module. -/
@[stacks 01CF "first exterior power map naturality"]
theorem degreeOne_naturality
    {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    f ≫ degreeOne N = degreeOne M ≫ map f 1 := sorry

/-- The inverse first-exterior-power isomorphisms are natural in the module. -/
@[stacks 01CF "inverse first exterior power naturality"]
theorem degreeOneIso_inv_naturality
    {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    map f 1 ≫ (degreeOneIso N).inv = (degreeOneIso M).inv ≫ f := sorry

/-- The degree-one maps form the forward natural transformation from modules to exterior powers.
-/
@[stacks 01CF "forward first exterior power natural transformation"]
noncomputable def degreeOneNatTrans :
    (𝟭 (ModuleCat.{max u v} R)) ⟶ exteriorPower.functor R 1 where
  app M := degreeOne M
  naturality _ _ f := degreeOne_naturality f

/-- The inverse degree-one maps form the inverse natural transformation. -/
@[stacks 01CF "inverse first exterior power natural transformation"]
noncomputable def degreeOneInvNatTrans :
    exteriorPower.functor R 1 ⟶ (𝟭 (ModuleCat.{max u v} R)) where
  app M := (degreeOneIso M).inv
  naturality _ _ f := degreeOneIso_inv_naturality f

/-- A component of the forward degree-one natural transformation is `degreeOne`. -/
@[simp, stacks 01CF "forward first exterior power natural transformation component"]
theorem degreeOneNatTrans_app (M : ModuleCat.{max u v} R) :
    (degreeOneNatTrans (R := R)).app M = degreeOne M := sorry

/-- A component of the inverse degree-one natural transformation is the inverse objectwise map. -/
@[simp, stacks 01CF "inverse first exterior power natural transformation component"]
theorem degreeOneInvNatTrans_app (M : ModuleCat.{max u v} R) :
    (degreeOneInvNatTrans (R := R)).app M = (degreeOneIso M).inv := sorry

/-- The forward degree-one natural transformation followed by its inverse is the identity. -/
@[simp, stacks 01CF "first exterior power natural transformation forward-inverse law"]
theorem degreeOneNatTrans_hom_inv_id :
    degreeOneNatTrans (R := R) ≫ degreeOneInvNatTrans (R := R) = 𝟙 _ := sorry

/-- The inverse degree-one natural transformation followed by its forward map is the identity. -/
@[simp, stacks 01CF "first exterior power natural transformation inverse-forward law"]
theorem degreeOneNatTrans_inv_hom_id :
    degreeOneInvNatTrans (R := R) ≫ degreeOneNatTrans (R := R) = 𝟙 _ := sorry

/-- Modules are naturally isomorphic to their first exterior powers. -/
@[stacks 01CF "natural first exterior power of modules"]
noncomputable def degreeOneNatIso :
    𝟭 (ModuleCat.{max u v} R) ≅ exteriorPower.functor R 1 :=
  { hom := degreeOneNatTrans (R := R)
    inv := degreeOneInvNatTrans (R := R)
    hom_inv_id := degreeOneNatTrans_hom_inv_id (R := R)
    inv_hom_id := degreeOneNatTrans_inv_hom_id (R := R) }

/-- The forward natural transformation of `degreeOneNatIso` is explicit. -/
@[simp, stacks 01CF "first exterior power natural isomorphism hom"]
theorem degreeOneNatIso_hom :
    (degreeOneNatIso (R := R)).hom = degreeOneNatTrans (R := R) := sorry

/-- The inverse natural transformation of `degreeOneNatIso` is explicit. -/
@[simp, stacks 01CF "first exterior power natural isomorphism inverse"]
theorem degreeOneNatIso_inv :
    (degreeOneNatIso (R := R)).inv = degreeOneInvNatTrans (R := R) := sorry

/-- A component of `degreeOneNatIso` is the objectwise first-exterior-power isomorphism. -/
@[simp, stacks 01CF "first exterior power natural isomorphism component"]
theorem degreeOneNatIso_app (M : ModuleCat.{max u v} R) :
    (degreeOneNatIso (R := R)).app M = degreeOneIso M := sorry

/-- The forward component of `degreeOneNatIso` is `degreeOne`. -/
@[simp, stacks 01CF "first exterior power natural isomorphism hom component"]
theorem degreeOneNatIso_hom_app (M : ModuleCat.{max u v} R) :
    (degreeOneNatIso (R := R)).hom.app M = degreeOne M := sorry

/-- The inverse component of `degreeOneNatIso` is the inverse objectwise map. -/
@[simp, stacks 01CF "first exterior power natural isomorphism inverse component"]
theorem degreeOneNatIso_inv_app (M : ModuleCat.{max u v} R) :
    (degreeOneNatIso (R := R)).inv.app M = (degreeOneIso M).inv := sorry

end ModuleCat.exteriorPower
