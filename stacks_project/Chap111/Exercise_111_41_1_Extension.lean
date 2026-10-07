module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import stacks_project.Chap111.Definition_111_41_2_Connecting
public import stacks_project.Chap111.Exercise_111_41_1_Cech

/-!
# Extensions of `𝒪` realizing coverwise Čech classes

Each class in `check H¹(𝒰, 𝒪)` is realized as the coverwise connecting value `δ(1)` of some
short exact sequence `0 → 𝒪 → E → 𝒪 → 0` of `𝒪_X`-modules on the two-chart cover.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.DoubledOrigin AlgebraicGeometry.RingedSpace
open CategoryTheory Opposite TopCat.Sheaf.Cohomology.Cech TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.DoubledOrigin

variable (k : Type u) [Field k]

/-- The structure sheaf of the doubled line, as an `𝒪_X`-module. -/
abbrev unitModule : (scheme k 1).toRingedSpace.Modules :=
  SheafOfModules.unit (scheme k 1).toRingedSpace.ringCatSheaf

/-- The underlying additive sheaf of an `𝒪`-module on the doubled line. -/
abbrev underlyingAbelianSheaf (E : (scheme k 1).toRingedSpace.Modules) :
    (scheme k 1).carrier.Sheaf AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (scheme k 1).toRingedSpace.ringCatSheaf).obj E

/-- The underlying additive morphism of an `𝒪`-module morphism on the doubled line. -/
def underlyingAbelianMap {E F : (scheme k 1).toRingedSpace.Modules} (f : E ⟶ F) :
    underlyingAbelianSheaf k E ⟶ underlyingAbelianSheaf k F :=
  (SheafOfModules.toSheaf (scheme k 1).toRingedSpace.ringCatSheaf).map f

/-- The composition of underlying additive maps of a composable pair of module morphisms. -/
theorem underlyingAbelianMap_comp {E F G : (scheme k 1).toRingedSpace.Modules}
    (f : E ⟶ F) (g : F ⟶ G) :
    underlyingAbelianMap k (f ≫ g) = underlyingAbelianMap k f ≫ underlyingAbelianMap k g :=
  sorry

/-- The two module maps of an extension of `𝒪` by `𝒪` compose to zero on underlying additive
sheaves. -/
theorem underlyingAbelianMap_comp_eq_zero {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0) :
    underlyingAbelianMap k ι ≫ underlyingAbelianMap k π = 0 :=
  sorry

/-- The underlying additive short complex of a module sequence `𝒪 ⟶ E ⟶ 𝒪` with zero composition. -/
def underlyingExtensionComplex {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0) :
    ShortComplex ((scheme k 1).carrier.Sheaf AddCommGrpCat.{u}) :=
  ShortComplex.mk (underlyingAbelianMap k ι) (underlyingAbelianMap k π)
    (underlyingAbelianMap_comp_eq_zero k ι π w)

/-- The global unit section `1` of `𝒪`, as an additive global section. -/
def unitGlobalSection : (underlyingAbelianSheaf k (unitModule k)).presheaf.obj (op ⊤) :=
  (1 : Γ(scheme k 1, ⊤))

/-- The global unit section is the multiplicative identity of `Γ(X, ⊤)`. -/
theorem unitGlobalSection_eq_one :
    unitGlobalSection k = (1 : Γ(scheme k 1, ⊤)) :=
  sorry

/-- Local additive sections of `E` on the two-chart cover. -/
abbrev localSectionFamily (E : (scheme k 1).toRingedSpace.Modules) : Type u :=
  ∀ i : ULift.{u} (Fin 2),
    (underlyingAbelianSheaf k E).presheaf.obj (op (chartCoverULift k i))

/-- A family of local `E`-sections lifts the global unit section of `𝒪`. -/
def IsLiftOfUnit {E : (scheme k 1).toRingedSpace.Modules}
    (π : E ⟶ unitModule k) (s : localSectionFamily k E) : Prop :=
  ∀ i : ULift.{u} (Fin 2),
    (underlyingAbelianMap k π).hom.app (op (chartCoverULift k i)) (s i) =
      (underlyingAbelianSheaf k (unitModule k)).presheaf.map
        (homOfLE (le_top : chartCoverULift k i ≤ ⊤)).op (unitGlobalSection k)

/-- The coverwise connecting class of a chosen lift of `1` on the two-chart cover. -/
def extensionCoverwiseClass {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0)
    (s : localSectionFamily k E) (hs : IsLiftOfUnit k π s) : cechH1 k :=
  coverwiseClass
    (@Lift.ofFamily (scheme k 1).carrier (underlyingExtensionComplex k ι π w)
      (unitGlobalSection k) (chartOpenCover k) s hs)

/-- A Čech class `c` is the coverwise connecting value `δ(1)` of the module extension
`0 → 𝒪 → E → 𝒪 → 0` on the two-chart cover `𝒰`. -/
def IsCoverwiseConnectingClass {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0) (c : cechH1 k) : Prop :=
  ∃ (s : localSectionFamily k E) (hs : IsLiftOfUnit k π s),
    extensionCoverwiseClass k ι π w s hs = c

/-- Unfolding of `IsCoverwiseConnectingClass` as existence of local lifts of `1` on `𝒰`. -/
theorem isCoverwiseConnectingClass_iff {E : (scheme k 1).toRingedSpace.Modules}
    (ι : unitModule k ⟶ E) (π : E ⟶ unitModule k) (w : ι ≫ π = 0) (c : cechH1 k) :
    IsCoverwiseConnectingClass k ι π w c ↔
      ∃ (s : localSectionFamily k E) (hs : IsLiftOfUnit k π s),
        extensionCoverwiseClass k ι π w s hs = c :=
  sorry

end AlgebraicGeometry.DoubledOrigin
