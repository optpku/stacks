module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType.Neighborhood
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Neighborhood properties of morphisms of finite-type module sheaves

The kernel of a map from a finite-type module sheaf to a coherent one is finite type. The generic
finite-kernel neighborhood criterion therefore turns injectivity at a stalk into monomorphy on a
neighborhood. The statement only requires a topological space with an arbitrary sheaf of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace SheafOfModules.Hom

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{u}}
variable {G F : SheafOfModules.{u} R}

/-- Injectivity of a stalk map extends to a monomorphism on some neighborhood when the source
is finite type and the target is coherent. -/
@[stacks 01C0]
theorem existsNeighborhood_mono_of_injective (φ : G ⟶ F) (x : X)
    [G.IsFiniteType] [F.IsCoherent]
    (hφx : Function.Injective
      (((SheafOfModules.stalkFunctor R x).map φ).hom)) :
    ∃ (U : Opens X) (_ : x ∈ U), Mono (SheafOfModules.Hom.over φ U) := sorry

/-- Injectivity of a commutative-ring stalk map extends to a monomorphism on some neighborhood
when the source is finite type and the target is coherent. -/
theorem existsNeighborhood_monoOfCommRing_of_injective
    {𝒪 : X.Sheaf CommRingCat.{u}}
    {G F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)}
    (φ : G ⟶ F) (x : X) [G.IsFiniteType] [F.IsCoherent]
    (hφx : Function.Injective
      (((SheafOfModules.stalkFunctorOfCommRing 𝒪 x).map φ).hom)) :
    ∃ (U : Opens X) (_ : x ∈ U), Mono (SheafOfModules.Hom.over φ U) := sorry

end SheafOfModules.Hom
