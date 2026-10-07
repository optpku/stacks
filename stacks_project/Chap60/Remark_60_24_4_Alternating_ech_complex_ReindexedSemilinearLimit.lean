module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe u
namespace CrystallineReindexedLimit

variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S)
variable (F : ℕᵒᵖ ⥤ ModuleCat.{u} R) (G : ℕᵒᵖ ⥤ ModuleCat.{u} S)
variable (k : ℕᵒᵖ ⥤ ℕᵒᵖ)
variable (α : k ⋙ F ⟶ G ⋙ ModuleCat.restrictScalars f)

/-- Reindex the source inverse limit, apply the specified stage maps,
then use the canonical fact that scalar restriction preserves limits. -/
noncomputable def underlyingMap :
    limit F ⟶ (ModuleCat.restrictScalars f).obj (limit G) :=
  limit.pre F k ≫ limMap α ≫ (preservesLimitIso (ModuleCat.restrictScalars f) G).inv

/-- The limit map uses the supplied stage map after the exact source
reindexing k; different envelope offsets therefore need not agree. -/
theorem underlyingMap_projection (e : ℕᵒᵖ) :
    underlyingMap f F G k α ≫ (ModuleCat.restrictScalars f).map (limit.π G e) =
      limit.π F (k.obj e) ≫ α.app e := by
  simp only [underlyingMap, Category.assoc, preservesLimitIso_inv_π]
  erw [limMap_π, ← Category.assoc, limit.pre_π]
  rfl

/-- The actual reindexed limit comparison, exposed as an f-semilinear
map. No inverse or comparison of unrelated module carriers is chosen. -/
noncomputable def map : (limit F : ModuleCat.{u} R) →ₛₗ[f] (limit G : ModuleCat.{u} S) where
  toFun := (underlyingMap f F G k α).hom
  map_add' := (underlyingMap f F G k α).hom.map_add
  map_smul' := (underlyingMap f F G k α).hom.map_smul

/-- Evaluation at a target stage computes precisely the specified map
from its reindexed source stage. -/
theorem map_projection (e : ℕᵒᵖ) (x : (limit F : ModuleCat.{u} R)) :
    limit.π G e (map f F G k α x) = α.app e (limit.π F (k.obj e) x) :=
  ConcreteCategory.congr_hom (underlyingMap_projection f F G k α e) x

end CrystallineReindexedLimit
