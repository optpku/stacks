module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Derivation
import StacksCheckRecall

/-!
# Canonical map from derivations to the tangent space

For any predeformation category, the special case `V = k` of `D ↦ f_{D,*}(x_0)` is a
canonical map `γ : Derivation Λ k k → tangentSpace p`, independent of the residue-fibre
object `x_0`.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)
variable [Functor.IsPredeformationCategory p]

/- 90.12.6.1: for any predeformation category `p`, the special case `V = k` of
`D ↦ f_{D,*}(x_0)` is the canonical map `γ : Derivation Λ k k → tangentSpace p`,
independent of the residue-fibre object `x_0`. Here `f_D` is `derivationToDualNumber D`,
and `tangentSpace p` is the type of isomorphism classes in the fibre over `dualNumber Λ k`. -/
@[stacks 06SV] #check (CategoryTheory.Functor.tangentSpace.ofDerivation p :
  Derivation Λ k k → Functor.tangentSpace p)
