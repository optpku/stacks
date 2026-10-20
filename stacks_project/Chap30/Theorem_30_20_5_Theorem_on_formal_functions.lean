module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FormalFunctions
import StacksCheckRecall

/-!
# Theorem on formal functions

For a proper morphism to the spectrum of a Noetherian ring and a coherent sheaf,
the descended comparisons `Hom.cohomology f F p ⧸ I ^ n • ⊤ ⟶ cohomology I f F p n`
induce an isomorphism from the I-adic completion of `Hom.cohomology f F p` to the
inverse limit of the quotient cohomology tower, and this comparison is a
homeomorphism of the two limit topologies.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace IdealPowerCohomology
namespace Quotient

variable {A : Type u} [CommRing A]
variable {X : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/- Theorem 30.20.5 (Theorem on formal functions)
The canonical comparison from completed cohomology to the inverse limit of
ideal-power quotient cohomology is an isomorphism of modules. -/
@[stacks 02OC] #check
  (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient.isIso_limitComparison :
    ∀ [IsNoetherianRing A] (I : Ideal A)
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (F : X.Modules) [F.IsCoherent] (p : ℕ),
      IsIso (limitComparison I f F p))

#check
  (AlgebraicGeometry.Scheme.Hom.IdealPowerCohomology.Quotient.isHomeomorph_limitComparison :
    ∀ [IsNoetherianRing A] (I : Ideal A)
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (F : X.Modules) [F.IsCoherent] (p : ℕ),
      @IsHomeomorph
      (AdicCompletion I (Hom.cohomology f F p))
      (limit (tower I f F p) : ModuleCat A)
      (⨅ n, TopologicalSpace.induced
        (AdicCompletion.eval I (Hom.cohomology f F p) n) ⊥)
      (Functor.limitTopology (tower I f F p))
      (limitComparison I f F p).hom)

end Quotient
end IdealPowerCohomology
end AlgebraicGeometry.Scheme.Hom
