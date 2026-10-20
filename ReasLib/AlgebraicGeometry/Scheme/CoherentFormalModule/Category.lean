module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Kernel
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# The abelian category of coherent formal modules

Cokernels and finite products are computed stagewise. Kernels are formed by taking the kernel
of the map of inverse-limit sheaves and then its ideal-power quotients; the stagewise kernel
system need not itself be a coherent formal module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The coimage-image comparison in coherent formal modules is an isomorphism. Affine locally,
both objects are the ideal-power quotient system of the same finite module over the completion. -/
instance coherentFormalModules_isIso_coimageImageComparison
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    {F G : CoherentFormalModules X I} (f : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison f) := sorry

/-- Coherent formal modules over a Noetherian scheme form an abelian category. -/
@[stacks 087X "(1)", implicit_reducible]
noncomputable def coherentFormalModules_abelian {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) : Abelian (CoherentFormalModules X I) :=
  Abelian.ofCoimageImageComparisonIsIso

attribute [instance] coherentFormalModules_abelian

end AlgebraicGeometry.Scheme
