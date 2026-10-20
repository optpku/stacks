module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Acyclicity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- If every nonempty finite intersection in an open cover of a scheme is affine, then the
Čech cohomology of a quasi-coherent module with respect to that cover is isomorphic to its
sheaf cohomology as a module over the ring of global sections. -/
theorem moduleCechCohomology_isomorphic_cohomology_of_affineIntersections
    {ι : Type u} (𝒰 : ι → X.Opens) (h𝒰 : TopologicalSpace.IsOpenCover 𝒰)
    (hAffine : ∀ n : ℕ, ∀ σ : Fin (n + 1) → ι, IsAffineOpen (⨅ a, 𝒰 (σ a)))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ) :
    IsIsomorphic
      (ModuleCech.cohomology (⊤ : X.Opens)
        (Opens.Cover.overFamily (⊤ : X.Opens) 𝒰 h𝒰.iSup_eq_top) ℱ p)
      (Modules.cohomology ℱ p) := sorry

end AlgebraicGeometry.Scheme
