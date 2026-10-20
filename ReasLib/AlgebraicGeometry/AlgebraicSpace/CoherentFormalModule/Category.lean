module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Kernel

/-!
# The abelian category of coherent formal modules
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The zero inverse system is a coherent formal module system over a Noetherian
algebraic space. -/
instance isCoherentFormalModuleSystem_containsZero {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] :
    (IsCoherentFormalModuleSystem I).ContainsZero :=
  sorry

/-- Coherent formal module systems over a Noetherian algebraic space are closed
under cokernels. -/
instance isCoherentFormalModuleSystem_isClosedUnderCokernels {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] :
    (IsCoherentFormalModuleSystem I).IsClosedUnderCokernels :=
  sorry

/-- Coherent formal module systems over a Noetherian algebraic space are closed
under finite products. -/
instance isCoherentFormalModuleSystem_isClosedUnderFiniteProducts
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    (IsCoherentFormalModuleSystem I).IsClosedUnderFiniteProducts :=
  sorry

/-- Étale locally the internal coimage and image are the same finite completed module. -/
instance coherentFormalModules_isIso_coimageImageComparison
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] {F G : CoherentFormalModules X I} (f : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison f) := sorry

/-- Coherent formal modules along a quasi-coherent ideal on a Noetherian
algebraic space form an abelian category. -/
@[stacks 089P "(1)", implicit_reducible]
noncomputable instance coherentFormalModules_abelian
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (I : IdealSubobject X) [IsQuasiCoherent I] : Abelian (CoherentFormalModules X I) :=
  Abelian.ofCoimageImageComparisonIsIso

end AlgebraicGeometry.AlgebraicSpace
