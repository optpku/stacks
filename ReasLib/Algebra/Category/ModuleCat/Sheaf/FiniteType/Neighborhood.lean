module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact
public import ReasLib.Topology.Sheaves.Abelian.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Neighborhood properties of finite-type module sheaves

These statements live on a topological space equipped with an arbitrary sheaf of rings. Finite
type turns stalkwise surjectivity into a neighborhood epimorphism and stalkwise vanishing into
neighborhood vanishing. Applied to a kernel, the same vanishing criterion gives neighborhood
monomorphisms and, together with a finite-type target, neighborhood isomorphisms. The
commutative-ring specialization is only retained where its differently bundled stalk object
requires a bridge.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace SheafOfModules.IsFiniteType

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{u}}
variable {G F : SheafOfModules.{u} R}

/-- A morphism to a finite-type module sheaf that is epic at a stalk is epic on some
neighborhood of that point. -/
@[stacks 01B8 "stalk epimorphism"]
theorem existsNeighborhood_epi (φ : G ⟶ F) (x : X) [F.IsFiniteType]
    (hφx : Epi ((SheafOfModules.stalkFunctor R x).map φ)) :
    ∃ (U : Opens X) (_ : x ∈ U), Epi (SheafOfModules.Hom.over φ U) := sorry

/-- Surjectivity of a stalk map into a finite-type module sheaf extends to an epimorphism on
some neighborhood. -/
@[stacks 01B8]
theorem existsNeighborhood_epi_of_surjective (φ : G ⟶ F) (x : X) [F.IsFiniteType]
    (hφx : Function.Surjective
      (((SheafOfModules.stalkFunctor R x).map φ).hom)) :
    ∃ (U : Opens X) (_ : x ∈ U), Epi (SheafOfModules.Hom.over φ U) := sorry

/-- A finite-type module sheaf whose stalk is zero vanishes on some neighborhood of that
point. -/
@[stacks 01B9]
theorem existsNeighborhood_isZero
    (F : SheafOfModules.{u} R) (x : X) [F.IsFiniteType]
    (hFx : IsZero ((SheafOfModules.stalkFunctor R x).obj F)) :
    ∃ (U : Opens X) (_ : x ∈ U), IsZero (F.over U) := sorry

/-- The commutative-ring-stalk formulation of neighborhood vanishing. This is a bridge to
`existsNeighborhood_isZero`, whose stalk is bundled over the underlying ring stalk. -/
@[stacks 01B9 "commutative-ring stalk bridge"]
theorem existsNeighborhood_isZeroOfCommRing
    {𝒪 : X.Sheaf CommRingCat.{u}}
    (F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪))
    (x : X) [F.IsFiniteType]
    (hFx : IsZero ((SheafOfModules.stalkFunctorOfCommRing 𝒪 x).obj F)) :
    ∃ (U : Opens X) (_ : x ∈ U), IsZero (F.over U) := sorry

/-- Surjectivity of a commutative-ring stalk map into a finite-type module sheaf extends to an
epimorphism on some neighborhood. -/
theorem existsNeighborhood_epiOfCommRing_of_surjective
    {𝒪 : X.Sheaf CommRingCat.{u}}
    {G F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)}
    (φ : G ⟶ F) (x : X) [F.IsFiniteType]
    (hφx : Function.Surjective
      (((SheafOfModules.stalkFunctorOfCommRing 𝒪 x).map φ).hom)) :
    ∃ (U : Opens X) (_ : x ∈ U), Epi (SheafOfModules.Hom.over φ U) := sorry

end SheafOfModules.IsFiniteType

namespace SheafOfModules.Hom

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{u}}
variable {G F : SheafOfModules.{u} R}

/-- A morphism that is monic at a stalk is monic on some neighborhood whenever its kernel is
finite type. -/
@[stacks 01C0 "finite-type kernel criterion"]
theorem existsNeighborhood_mono (φ : G ⟶ F) (x : X)
    [(kernel φ).IsFiniteType]
    (hφx : Mono ((SheafOfModules.stalkFunctor R x).map φ)) :
    ∃ (U : Opens X) (_ : x ∈ U), Mono (SheafOfModules.Hom.over φ U) := sorry

/-- A morphism that is an isomorphism at a stalk is an isomorphism on some neighborhood when
its kernel and target are finite type. -/
@[stacks 01Y3 "(4), categorical finite criterion"]
theorem existsNeighborhood_isIso (φ : G ⟶ F) (x : X)
    [(kernel φ).IsFiniteType] [F.IsFiniteType]
    (hφx : IsIso ((SheafOfModules.stalkFunctor R x).map φ)) :
    ∃ (U : Opens X) (_ : x ∈ U), IsIso (SheafOfModules.Hom.over φ U) := sorry

/-- Bijectivity of a stalk map extends to an isomorphism on some neighborhood when the kernel
and target are finite type. -/
@[stacks 01Y3 "(4), finite criterion"]
theorem existsNeighborhood_isIso_of_bijective (φ : G ⟶ F) (x : X)
    [(kernel φ).IsFiniteType] [F.IsFiniteType]
    (hφx : Function.Bijective
      (((SheafOfModules.stalkFunctor R x).map φ).hom)) :
    ∃ (U : Opens X) (_ : x ∈ U), IsIso (SheafOfModules.Hom.over φ U) := sorry

/-- Bijectivity of a commutative-ring stalk map extends to an isomorphism on some neighborhood
when the kernel and target are finite type. -/
theorem existsNeighborhood_isIsoOfCommRing_of_bijective
    {𝒪 : X.Sheaf CommRingCat.{u}}
    {G F : SheafOfModules.{u} (TopCat.Sheaf.ringSheafOfComm 𝒪)}
    (φ : G ⟶ F) (x : X) [(kernel φ).IsFiniteType] [F.IsFiniteType]
    (hφx : Function.Bijective
      (((SheafOfModules.stalkFunctorOfCommRing 𝒪 x).map φ).hom)) :
    ∃ (U : Opens X) (_ : x ∈ U), IsIso (SheafOfModules.Hom.over φ U) := sorry

end SheafOfModules.Hom
