module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.MinimalSpecialization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Support of weakly associated points

The weakly associated locus of a quasi-coherent module sheaf on an algebraic space is contained
in its support. Conversely, a support point whose local ring has dimension zero is weakly
associated. For a finite-type quasi-coherent module, every point of its scheme-theoretic
support whose local ring has dimension zero maps to a weakly associated point.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Every weakly associated point of a quasi-coherent module on an algebraic space lies in its
support. -/
theorem weakAss_subset_support (F : X.Modules) [F.IsQuasicoherent] :
    F.weakAss ⊆ F.moduleSupport :=
  sorry

/-- A point in the support of a quasi-coherent module on an algebraic space is weakly
associated if its local ring has dimension zero. -/
@[stacks 0CUL]
theorem mem_weakAss_of_codimZero_moduleSupport (F : X.Modules) [F.IsQuasicoherent]
    {x : Points X} (hx : x ∈ F.moduleSupport) (hdim : localRingDimAt x = 0) :
    x ∈ F.weakAss :=
  sorry

/-- A point of the scheme-theoretic support of a finite-type quasi-coherent module whose
local ring has dimension zero maps to a weakly associated point of the module. -/
@[stacks 0CUL]
theorem mem_weakAss_of_codimZero_schemeTheoreticSupport
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    {z : Points (schemeTheoreticSupport F).X} (hdim : localRingDimAt z = 0) :
    Points.map (schemeTheoreticSupport F).ι z ∈ F.weakAss :=
  sorry

/-- Every minimal specialization point of the support of a quasi-coherent module on a
decent algebraic space is weakly associated to the module. -/
@[stacks 0CUM]
theorem minimalSpecializationPoints_support_subset_weakAss
    (F : X.Modules) [F.IsQuasicoherent] [IsDecent X] :
    X.minimalSpecializationPoints F.moduleSupport ⊆ F.weakAss :=
  sorry

/-- If `x` lies in the support of a quasi-coherent module `F` on a decent
algebraic space and no distinct point of that support specializes to `x`, then
`x` is weakly associated to `F`. -/
theorem mem_weakAss_of_mem_moduleSupport_of_eq_of_specializes
    (F : X.Modules) [F.IsQuasicoherent] [IsDecent X] {x : Points X}
    (hx : x ∈ F.moduleSupport)
    (hmin : ∀ ⦃y : Points X⦄, y ∈ F.moduleSupport → Specializes y x → y = x) :
    x ∈ F.weakAss :=
  minimalSpecializationPoints_support_subset_weakAss F ⟨hx, hmin⟩

end AlgebraicGeometry.AlgebraicSpace.Modules
