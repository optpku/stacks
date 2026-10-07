module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PontryaginDual.Representability.Naturality
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedModule
open PontryaginRepresentable
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable (k : ℤ)

/- Lemma 22.19.3 (1) (09K4): `M ↦ Hom_A(M, Aᵛ[k])` and `M ↦ Z^k(Mᵛ)` are naturally
isomorphic as contravariant functors in `M`. -/
@[stacks 09K4] #check
  (homCyclesIso A k : Functor.hom A k ≅ Functor.cycles A k)

/- Lemma 22.19.3 (2) (09K4): `M ↦ Hom_K(M, Aᵛ[k])` and `M ↦ H^k(Mᵛ)` are naturally
isomorphic as contravariant functors in `M`. -/
@[stacks 09K4] #check
  (homotopyHomologyIso A k : Functor.homotopy A k ≅ Functor.homology A k)
