module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.DifferentialForms
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

variable {X' X S' S : Scheme.{u}}
variable {f : X' ⟶ X} {g : S' ⟶ S} {h : X ⟶ S} {h' : X' ⟶ S'}
variable (sq : CommSq f h' h g) [Etale f] [Etale g] (p : ℕ)

/- Lemma 50.2.2: for a commutative square of schemes with étale horizontal maps, the
canonical map `f^* Ω^p_{X/S} ⟶ Ω^p_{X'/S'}` is an isomorphism. -/
@[stacks 0FLV]
#check (AlgebraicGeometry.Scheme.RelativeDifferentials.formComparison_isIso_of_etale sq p :
  IsIso (formComparison sq p))

end AlgebraicGeometry.Scheme.RelativeDifferentials
