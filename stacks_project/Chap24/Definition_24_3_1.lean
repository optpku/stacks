module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
import StacksCheckRecall

/-!
# Definition 24.3.1

Sheaves of graded 𝒪-algebras on a ringed site, and their homomorphisms, are owned by
`SheafOfModules.RingedSite.GradedAlgebraSheaf`.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable (𝒜 ℬ : GradedAlgebraSheaf 𝒪 ℤ)

/- Definition 24.3.1 (1): a sheaf of graded 𝒪-algebras is a ℤ-indexed family of 𝒪-modules
with associative 𝒪-bilinear multiplication maps 𝒜 n × 𝒜 m → 𝒜 (n + m) and a global
section 1 of 𝒜 0 that is a two-sided identity. -/
@[stacks 0FQW]
#check GradedAlgebraSheaf 𝒪 ℤ

#check 𝒜.obj
#check 𝒜.one
#check 𝒜.mul

/- Definition 24.3.1 (2): a homomorphism of graded 𝒪-algebras is a family of 𝒪-module
maps 𝒜 n ⟶ ℬ n compatible with the multiplication maps. -/
@[stacks 0FQW]
#check GradedAlgebraSheaf.Hom 𝒜 ℬ

end
