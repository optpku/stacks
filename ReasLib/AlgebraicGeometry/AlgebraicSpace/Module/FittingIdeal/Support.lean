module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport

/-!
# Zeroth Fitting ideals and support on algebraic spaces

The closed subspace defined by the zeroth Fitting ideal contains the
scheme-theoretic support, has the same underlying point-set, and carries a
finite-type quasi-coherent descent of the module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The Fitting ideal of a finite-type quasi-coherent module is a quasi-coherent
ideal subobject of the structure sheaf. -/
instance instIdealIsQuasiCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (i : ℕ) :
    IsQuasiCoherent (AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf F i) where
  quasiCoherent := AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf.instIsQuasicoherent F i

/-- The closed subspace cut out by the zeroth Fitting ideal of a finite-type
quasi-coherent module. -/
def fittingIdealZeroSubspace {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] : ClosedSubspace X :=
  ClosedSubspace.ofQuasiCoherentIdeal (AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf F 0)

/-- The inclusion of the zeroth Fitting closed subspace is the subscheme
inclusion defined by the zeroth Fitting ideal. -/
theorem fittingIdealZeroSubspace_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (fittingIdealZeroSubspace F).ι =
      subschemeι (AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf F 0) :=
  rfl

/-- The kernel ideal sheaf of the zeroth Fitting closed subspace is the zeroth
Fitting ideal. -/
theorem fittingIdealZeroSubspace_idealSheaf {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (fittingIdealZeroSubspace F).idealSheaf =
      AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf F 0 :=
  ClosedSubspace.ofQuasiCoherentIdeal_idealSheaf
    (AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf F 0)

/-- The zeroth Fitting closed subspace has defining ideal the zeroth Fitting
ideal, and its inclusion is a closed immersion. -/
theorem fittingIdealZeroSubspace_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (fittingIdealZeroSubspace F).idealSheaf =
        AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf F 0 ∧
      IsClosedImmersion (fittingIdealZeroSubspace F).ι :=
  ⟨fittingIdealZeroSubspace_idealSheaf F, (fittingIdealZeroSubspace F).isClosedImmersion⟩

/-- The zeroth Fitting ideal is contained in the defining ideal of the
scheme-theoretic support. -/
theorem fittingIdealSheaf_zero_le_schemeTheoreticSupport
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf F 0 ≤
      (schemeTheoreticSupport F).idealSheaf :=
  sorry

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]

/-- The scheme-theoretic support of a finite-type quasi-coherent module factors
through the closed subspace cut out by its zeroth Fitting ideal. -/
theorem schemeTheoreticSupport_le_fittingIdealZeroSubspace
    {Z : AlgebraicSpace S} (i : Z ⟶ X) [IsSchemeTheoreticSupport F i] :
    ∃ f : Z ⟶ (fittingIdealZeroSubspace F).X,
      f ≫ (fittingIdealZeroSubspace F).ι = i :=
  sorry

/-- The point-set of the scheme-theoretic support and that of the zeroth
Fitting closed subspace both equal the support of the module. -/
theorem fittingIdealZeroSubspace_pointsSet_eq_moduleSupport
    {Z : AlgebraicSpace S} (i : Z ⟶ X) [IsSchemeTheoreticSupport F i] :
    Set.range (Points.map i) = (fittingIdealZeroSubspace F).pointsSet ∧
      (fittingIdealZeroSubspace F).pointsSet = moduleSupport F :=
  sorry

/-- A finite-type quasi-coherent module is the pushforward of a finite-type
quasi-coherent module on its zeroth Fitting closed subspace. -/
theorem exists_finiteType_module_pushforward_fittingIdealZero :
    ∃ G0 : (fittingIdealZeroSubspace F).X.Modules,
      G0.IsQuasicoherent ∧ G0.IsFiniteType ∧
        Nonempty ((pushforward (fittingIdealZeroSubspace F).ι).obj G0 ≅ F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
