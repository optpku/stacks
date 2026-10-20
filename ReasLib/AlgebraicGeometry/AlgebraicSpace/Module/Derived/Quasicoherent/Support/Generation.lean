module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Support.Shift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.Topology.Sets.Closeds

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn

/-- The property of having quasi-coherent cohomology supported on a subset is
triangulated. -/
instance quasiCoherentSupportedOn_isTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S)
    (T : Set (Points X)) :
    (quasiCoherentSupportedOn X T).IsTriangulated := sorry

/-- The derived category of quasi-coherent modules supported on a subset admits
coproducts indexed by types in the ambient universe. -/
instance hasCoproducts {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Set (Points X)) :
    CategoryTheory.Limits.HasCoproducts.{u} (SupportedOn X T) := sorry

/-- If `X` is a quasi-compact and quasi-separated algebraic space and `T` is a closed
subset with quasi-compact complement, then the category of derived quasi-coherent
modules supported on `T` has a perfect weak generator. -/
theorem exists_isPerfect_isWeakGenerator {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (T : Closeds (Points X))
    (hT : IsCompact (T.compl : Set (Points X))) :
    ∃ P : SupportedOn X (T : Set (Points X)),
      ModuleDerived.IsPerfect P.obj ∧ IsWeakGenerator P := sorry

/-- A perfect weak generator of supported derived quasi-coherent modules on a
quasi-compact and quasi-separated algebraic space classically generates all supported
perfect objects when the support is closed with quasi-compact complement. -/
theorem isClassicalGeneratorOfPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (T : Closeds (Points X))
    (hT : IsCompact (T.compl : Set (Points X)))
    (G : SupportedOn X (T : Set (Points X)))
    (hG_perfect : ModuleDerived.IsPerfect G.obj)
    (hG_generator : IsWeakGenerator G) :
    (fun E : SupportedOn X (T : Set (Points X)) ↦ ModuleDerived.IsPerfect E.obj) ≤
      (CategoryTheory.ObjectProperty.singleton G).triangEnvelope := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn
