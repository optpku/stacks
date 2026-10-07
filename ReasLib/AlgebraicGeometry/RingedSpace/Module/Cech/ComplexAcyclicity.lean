module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Cofinal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Acyclic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basiswise acyclicity for complexes of module sheaves

The property in this file separates the reusable cohomological input from any particular Cech
comparison construction.  It records acyclicity of the terms, differential cokernels, and
cohomology objects of a complex, together with finite-intersection stability of an indexed family
of opens.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech

variable {X : RingedSpace.{u}} {ι : Type u}

/-- An indexed open family and a cochain complex satisfy the basiswise acyclicity hypotheses used
to compare an unbounded Cech total complex with derived global sections. -/
@[stacks 08C2 "basiswise acyclicity for a complex of module sheaves"]
structure BasiswiseAcyclic (𝒰 : ι → Opens X.carrier)
    (K : CochainComplex X.Modules ℤ) (B : Set (Opens X.carrier)) : Prop where
  /-- The opens in the family and all their nonempty finite intersections belong to `B`. -/
  family : IsBasisStableFamily B 𝒰
  /-- Every term of the complex is cohomologically acyclic on `B`. -/
  term (q : ℤ) : ModuleCohomology.IsAcyclicOn (K.X q) B
  /-- Every cokernel of an incoming differential is cohomologically acyclic on `B`. -/
  cokernel (q : ℤ) : ModuleCohomology.IsAcyclicOn (Limits.cokernel (K.d (q - 1) q)) B
  /-- Every cohomology object of the complex is cohomologically acyclic on `B`. -/
  homology (q : ℤ) : ModuleCohomology.IsAcyclicOn (K.homology q) B

namespace BasiswiseAcyclic

/-- Every nonempty finite intersection of the indexed family belongs to the chosen basis. -/
@[stacks 08C2 "finite intersections in a Cech-acyclic basis"]
theorem intersection_mem {𝒰 : ι → Opens X.carrier} {K : CochainComplex X.Modules ℤ}
    {B : Set (Opens X.carrier)} (hK : BasiswiseAcyclic 𝒰 K B)
    (p : ℕ) (σ : Fin (p + 1) → ι) :
    (⨅ a, 𝒰 (σ a)) ∈ B := sorry

/-- Positive open cohomology of a term vanishes on every basis member. -/
@[stacks 08C2 "basiswise acyclicity of complex terms"]
theorem term_isZero {𝒰 : ι → Opens X.carrier} {K : CochainComplex X.Modules ℤ}
    {B : Set (Opens X.carrier)} (hK : BasiswiseAcyclic 𝒰 K B)
    {U : Opens X.carrier} (hU : U ∈ B) (p : ℕ) (hp : 0 < p) (q : ℤ) :
    IsZero (moduleCohomologyAtOpen U (K.X q) p) := sorry

/-- Positive open cohomology of a differential cokernel vanishes on every basis member. -/
@[stacks 08C2 "basiswise acyclicity of differential cokernels"]
theorem cokernel_isZero {𝒰 : ι → Opens X.carrier} {K : CochainComplex X.Modules ℤ}
    {B : Set (Opens X.carrier)} (hK : BasiswiseAcyclic 𝒰 K B)
    {U : Opens X.carrier} (hU : U ∈ B) (p : ℕ) (hp : 0 < p) (q : ℤ) :
    IsZero (moduleCohomologyAtOpen U (Limits.cokernel (K.d (q - 1) q)) p) := sorry

/-- Positive open cohomology of a cohomology object vanishes on every basis member. -/
@[stacks 08C2 "basiswise acyclicity of complex cohomology objects"]
theorem homology_isZero {𝒰 : ι → Opens X.carrier} {K : CochainComplex X.Modules ℤ}
    {B : Set (Opens X.carrier)} (hK : BasiswiseAcyclic 𝒰 K B)
    {U : Opens X.carrier} (hU : U ∈ B) (p : ℕ) (hp : 0 < p) (q : ℤ) :
    IsZero (moduleCohomologyAtOpen U (K.homology q) p) := sorry

end BasiswiseAcyclic

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The expanded source-facing form of `BasiswiseAcyclic`, using ordinary cohomology of the
underlying additive sheaves. -/
@[stacks 08C2 "underlying sheaf basiswise acyclicity for a complex"]
def UnderlyingBasiswiseAcyclic (𝒰 : ι → Opens X.carrier)
    (K : CochainComplex X.Modules ℤ) (B : Set (Opens X.carrier)) : Prop :=
  (∀ p : ℕ, ∀ σ : Fin (p + 1) → ι, (⨅ a, 𝒰 (σ a)) ∈ B) ∧
    (∀ ⦃U : Opens X.carrier⦄, U ∈ B → ∀ p : ℕ, 0 < p → ∀ q : ℤ,
      IsZero (((moduleUnderlyingSheaf X).obj (K.X q)).H' p U)) ∧
    (∀ ⦃U : Opens X.carrier⦄, U ∈ B → ∀ p : ℕ, 0 < p → ∀ q : ℤ,
      IsZero (((moduleUnderlyingSheaf X).obj
        (Limits.cokernel (K.d (q - 1) q))).H' p U)) ∧
    ∀ ⦃U : Opens X.carrier⦄, U ∈ B → ∀ p : ℕ, 0 < p → ∀ q : ℤ,
      IsZero (((moduleUnderlyingSheaf X).obj (K.homology q)).H' p U)

namespace BasiswiseAcyclic

/-- The bundled module-valued predicate is equivalent to the expanded underlying-sheaf
formulation appearing in Lemma 20.40.2. -/
@[stacks 08C2 "underlying sheaf form of basiswise complex acyclicity"]
theorem iff_underlying {𝒰 : ι → Opens X.carrier} {K : CochainComplex X.Modules ℤ}
    {B : Set (Opens X.carrier)} :
    BasiswiseAcyclic 𝒰 K B ↔ UnderlyingBasiswiseAcyclic 𝒰 K B := sorry

end BasiswiseAcyclic

end AlgebraicGeometry.RingedSpace.ModuleCech
