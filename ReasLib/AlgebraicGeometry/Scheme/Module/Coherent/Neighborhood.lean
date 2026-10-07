module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Neighborhood
public import ReasLib.AlgebraicGeometry.Noetherian.Topology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Neighborhood

/-!
# Neighborhood properties of coherent module sheaves

On a locally Noetherian scheme, stalkwise vanishing of a coherent module sheaf and stalkwise
injectivity, surjectivity, or bijectivity of a morphism of coherent module sheaves persist on an
open neighborhood.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsCoherent

/-- A coherent module sheaf with zero stalk at a point vanishes on some open neighborhood of
that point. -/
theorem existsNeighborhood_isZero
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : X)
    (hFx : IsZero (RingedSpace.stalkModuleCat F x)) :
    ∃ (U : X.Opens) (_ : x ∈ U), IsZero (F.over U) := sorry

/-- A morphism of coherent module sheaves that is injective at a stalk is a monomorphism on
some open neighborhood of the point. -/
theorem existsNeighborhood_mono_of_injective
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
    (φ : G ⟶ F) (x : X)
    (hφx : Function.Injective (RingedSpace.moduleStalkMap x φ)) :
    ∃ (U : X.Opens) (_ : x ∈ U), Mono (SheafOfModules.Hom.over φ U) := sorry

/-- A morphism of coherent module sheaves that is surjective at a stalk is an epimorphism on
some open neighborhood of the point. -/
theorem existsNeighborhood_epi_of_surjective
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
    (φ : G ⟶ F) (x : X)
    (hφx : Function.Surjective (RingedSpace.moduleStalkMap x φ)) :
    ∃ (U : X.Opens) (_ : x ∈ U), Epi (SheafOfModules.Hom.over φ U) := sorry

/-- A morphism of coherent module sheaves that is bijective at a stalk is an isomorphism on
some open neighborhood of the point. -/
theorem existsNeighborhood_isIso_of_bijective
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
    (φ : G ⟶ F) (x : X)
    (hφx : Function.Bijective (RingedSpace.moduleStalkMap x φ)) :
    ∃ (U : X.Opens) (_ : x ∈ U), IsIso (SheafOfModules.Hom.over φ U) := sorry

/-- A morphism between stalks of coherent module sheaves on a locally Noetherian scheme
extends to a morphism between their restrictions on some open neighborhood. -/
theorem existsNeighborhood_restrictHom_of_stalkHom
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
    (x : X) (ψ : RingedSpace.stalkModuleCat G x ⟶ RingedSpace.stalkModuleCat F x) :
    ∃ (U : X.Opens) (hxU : x ∈ U)
      (φ : (restrictFunctor U.ι).obj G ⟶ (restrictFunctor U.ι).obj F),
      stalkAddHomOfRestrictHom x U hxU φ =
        (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map ψ := sorry

end AlgebraicGeometry.Scheme.Modules.IsCoherent
