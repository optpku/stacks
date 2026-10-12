/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalCohomology.Cutoff
public import ReasLib.RingTheory.Catenary.Universally

@[expose] public section

universe u v w

namespace Module.LocalCohomology

/-- Extending an ideal along a finite algebra map preserves the local-cohomology
finiteness cutoff for finite modules over a universally catenary base ring. -/
theorem cutoff_map_eq_of_finite
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [IsNoetherianRing B] [UniversallyCatenaryRing.{u, v} A]
    (I : Ideal A) (M : Type w) [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] [Module.Finite B M] :
    -- Local instance justification (search instability): `Module.Finite.trans` needs the intermediate ring `B`, which is not inferable from `A` and `M`, so this derived instance is scoped to the conclusion.
    letI : Module.Finite A M := Module.Finite.trans B M
    cutoff (I.map (algebraMap A B)) M = cutoff I M := sorry

end Module.LocalCohomology
