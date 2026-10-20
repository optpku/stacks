module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Support
import StacksCheckRecall

/-!
# Lemma 71.2.7

On a decent algebraic space, every minimal specialization point of the support
of a quasi-coherent module is weakly associated to that module.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.2.7: for a scheme `S`, a decent algebraic space `X` over `S`
(for example a quasi-separated or locally separated algebraic space), and a
quasi-coherent `𝒪_X`-module `F`, every minimal specialization point of
`F.moduleSupport` is weakly associated to `F`. -/
@[stacks 0CUM]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.minimalSpecializationPoints_support_subset_weakAss :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
      [F.IsQuasicoherent] [IsDecent X],
      X.minimalSpecializationPoints F.moduleSupport ⊆ F.weakAss)

/- If `x` lies in the support of a quasi-coherent module `F` on a decent
algebraic space and no distinct point of that support specializes to `x`, then
`x` is weakly associated to `F`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_of_mem_moduleSupport_of_eq_of_specializes :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
      [F.IsQuasicoherent] [IsDecent X] {x : Points X},
      x ∈ F.moduleSupport →
      (∀ ⦃y : Points X⦄, y ∈ F.moduleSupport → Specializes y x → y = x) →
      x ∈ F.weakAss)
