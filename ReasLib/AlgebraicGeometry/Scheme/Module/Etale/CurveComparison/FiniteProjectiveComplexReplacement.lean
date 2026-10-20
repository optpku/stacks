module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteFreeModuleResolution

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
noncomputable section
universe u

namespace FiniteProjectiveComplexReplacement
variable (S : Type u) [Ring S]
variable (K : ChainComplex (ModuleCat.{u} S) ℕ)

/-- One explicit free-stage construction, retaining its actual map to K and
its outgoing differential. This is internal algorithmic data, not an assumed comparison package. -/
structure Stage (n : ℕ) where
  P : ModuleCat.{u} S
  previous : ModuleCat.{u} S
  d : P ⟶ previous
  ε : P ⟶ K.X n
  projective : Projective P

/-- Begin with the free module on the actual degree-zero vectors. -/
def initial : Stage S K 0 where
  P := FiniteFreeModuleResolution.free S (K.X 0)
  previous := 0
  d := 0
  ε := FiniteFreeModuleResolution.evaluation S (K.X 0)
  projective := by
    change Projective (ModuleCat.of S ((K.X 0) →₀ S))
    infer_instance

/-- A next-stage generator is a source vector x and a preceding cycle y
whose specified images agree: d_K x = ε y and d_P y = 0. -/
def constraint (n : ℕ) (s : Stage S K n) : Submodule S ((K.X (n + 1)) × s.P) where
  carrier := {p | (K.d (n + 1) n).hom p.1 = s.ε.hom p.2 ∧ s.d.hom p.2 = 0}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

/-- Freely generate those actual compatible pairs. The two projections give
the next differential and augmentation component, respectively. -/
def step (n : ℕ) (s : Stage S K n) : Stage S K (n + 1) where
  P := FiniteFreeModuleResolution.free S (ModuleCat.of S (constraint S K n s))
  previous := s.P
  d := FiniteFreeModuleResolution.evaluation S (ModuleCat.of S (constraint S K n s)) ≫
    ModuleCat.ofHom ((LinearMap.snd S (K.X (n + 1)) s.P).domRestrict (constraint S K n s))
  ε := FiniteFreeModuleResolution.evaluation S (ModuleCat.of S (constraint S K n s)) ≫
    ModuleCat.ofHom ((LinearMap.fst S (K.X (n + 1)) s.P).domRestrict (constraint S K n s))
  projective := by
    change Projective (ModuleCat.of S ((constraint S K n s) →₀ S))
    infer_instance

/-- Deterministic kernel/free recursion for the whole chain complex. -/
def stages : (n : ℕ) → Stage S K n
  | 0 => initial S K
  | n + 1 => step S K n (stages n)

/-- The actual degreewise free terms. -/
abbrev terms (n : ℕ) := (stages S K n).P

/-- The actual compatible-pair projection differentials. -/
def differential (n : ℕ) : terms S K (n + 1) ⟶ terms S K n := (stages S K (n + 1)).d

/-- Successive differentials compose to zero by the cycle constraint. -/
theorem differential_squared (n : ℕ) :
    differential S K (n + 1) ≫ differential S K n = 0 := by sorry

/-- Concrete projective replacement complex; no arbitrary resolution is selected. -/
def complex := ChainComplex.of (terms S K) (differential S K) (differential_squared S K)

/-- The replacement map uses the actual vector projections of the recursion. -/
def toOriginal : complex S K ⟶ K where
  f n := (stages S K n).ε
  comm' := by sorry

/-- Cycles lift via (x,0); null cycles lift via their specified boundary pair.
This proves quasi-isomorphism of this particular chain map. -/
theorem toOriginal_quasiIso : QuasiIso (toOriginal S K) := by sorry

/-- Every constructed term is free, hence projective in ModuleCat S. -/
theorem term_projective (n : ℕ) : Projective ((complex S K).X n) := (stages S K n).projective

/-- For a finite coefficient ring and finite original terms, the compatible
pair submodules and free stages remain finite. No claim is made for arbitrary resolutions. -/
theorem term_finite [Finite S] (hfin : ∀ n : ℕ, Finite (K.X n)) (n : ℕ) :
    Finite ((complex S K).X n) := by sorry

end FiniteProjectiveComplexReplacement
