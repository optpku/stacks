module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Relative

/-!
# Relative associated points on affine opens

This file compares the relative assassin of affine-open sections with the relative assassin of a
quasi-coherent scheme module.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.relativeAssassin

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)

/-- The residue-field base change of the sections of a scheme module on an affine open, bundled
as a module over the section ring of that open. -/
noncomputable def sectionsResidueModule
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) (p : PrimeSpectrum (Γ(X, U))) :
    ModuleCat (Γ(X, U)) :=
  let _ : Algebra Γ(S, V) Γ(X, U) := f.sectionsAlgebra V U e
  let _ : Module Γ(S, V) Γ(ℱ, U) := f.sectionsModule V U e ℱ
  let _ : IsScalarTower Γ(S, V) Γ(X, U) Γ(ℱ, U) :=
    IsScalarTower.of_compHom Γ(S, V) Γ(X, U) Γ(ℱ, U)
  ModuleCat.of (Γ(X, U))
    (TensorProduct (Γ(S, V)) (Γ(ℱ, U)) ((p.asIdeal.under (Γ(S, V))).ResidueField))

/-- The relative assassin of affine-open sections over the induced map of section rings. -/
def sections (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    Set (PrimeSpectrum (Γ(X, U))) :=
  let _ : Algebra Γ(S, V) Γ(X, U) := f.sectionsAlgebra V U e
  let _ : Module Γ(S, V) Γ(ℱ, U) := f.sectionsModule V U e ℱ
  let _ : IsScalarTower Γ(S, V) Γ(X, U) Γ(ℱ, U) :=
    IsScalarTower.of_compHom Γ(S, V) Γ(X, U) Γ(ℱ, U)
  _root_.relativeAssassin (Γ(S, V)) (Γ(X, U)) (Γ(ℱ, U))

/-- A prime belongs to the relative assassin of affine-open sections exactly when it is
associated to the corresponding residue-field base change of the section module. -/
@[simp]
theorem mem_sections_iff
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) (p : PrimeSpectrum (Γ(X, U))) :
    p ∈ sections f ℱ U V e ↔
      p.asIdeal ∈ associatedPrimesOfModule (Γ(X, U)) (sectionsResidueModule f ℱ U V e p) := by
  rfl

/-- An affine-open prime in the relative assassin of sections determines a point in the
scheme-theoretic relative assassin. -/
theorem fromSpec_mem_of_mem_sections
    [ℱ.IsQuasicoherent]
    {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (p : PrimeSpectrum (Γ(X, U)))
    (hp : p ∈ sections f ℱ U V e) :
    hU.fromSpec p ∈ AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ := sorry

/-- If every fiber is locally Noetherian, an affine-open prime lies in the relative assassin of
sections exactly when its corresponding point lies in the scheme-theoretic relative assassin. -/
theorem mem_sections_iff_fromSpec_mem_of_isLocallyNoetherian_fibers
    [ℱ.IsQuasicoherent]
    {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (hfib : ∀ s : S, IsLocallyNoetherian (Scheme.Hom.fiber f s))
    (p : PrimeSpectrum (Γ(X, U))) :
    p ∈ sections f ℱ U V e ↔
      hU.fromSpec p ∈ AlgebraicGeometry.Scheme.Modules.relativeAssassin f ℱ := sorry

end AlgebraicGeometry.Scheme.Modules.relativeAssassin
