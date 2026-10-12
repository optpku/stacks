/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.QuasiCoherent
public import ReasLib.RingTheory.Ideal.Power.DGA
public import ReasLib.RingTheory.Sequence.Koszul.Power
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

section


variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R)

/- The first system is now the positive tower `R / I ^ (n + 1)` as actual cochain DGAs, rather than
only an unbased inverse system of commutative rings. -/
#check
  (Ideal.Power.dgaSystem I : ℕᵒᵖ ⥤ CochainDGAlgebra.{u, u} R)

/- Proposition 24.35.4 (tag 0GZK), first category: quasi-coherent objects in the global derived
category of module systems over the positive ideal-power quotient DGA tower. -/
@[stacks 0GZK "global QC over the ideal-power quotient DGA tower"]
#check
  (DifferentialGradedModule.InverseSystem.Derived.QC
    (Ideal.Power.dgaSystem I) : Type (u + 1))

/- Proposition 24.35.4 (tag 0GZK), third category: the canonical full subcategory of
`I`-derived-complete objects. -/
@[stacks 0GZK "derived-complete target category"]
#check
  ((DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory : Type (u + 1))

end


section PoweredKoszul

variable {R : Type u} [CommRing R]
variable {r : ℕ} (f : Fin r → R)

/- The second category uses the canonical powered Koszul cochain-DGA tower. -/
@[stacks 0GZK "global QC over the powered Koszul DGA tower"]
#check
  (DifferentialGradedModule.InverseSystem.Derived.QC
    (KoszulComplex.powerDGASystem f) : Type (u + 1))

end PoweredKoszul
