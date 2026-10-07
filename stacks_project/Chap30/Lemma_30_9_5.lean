module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Neighborhood
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 30.9.5 (1) (01Y3): a coherent module sheaf on a locally Noetherian scheme which has zero
stalk at a point vanishes on some neighborhood of that point. -/
@[stacks 01Y3 "(1)"]
#check (AlgebraicGeometry.Scheme.Modules.IsCoherent.existsNeighborhood_isZero :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (F : X.Modules) [F.IsCoherent] (x : X)
      (_ : IsZero (RingedSpace.stalkModuleCat F x)),
    ∃ (U : X.Opens) (_ : x ∈ U), IsZero (F.over U))

/- Lemma 30.9.5 (2) (01Y3): a morphism of coherent module sheaves on a locally Noetherian scheme
which is injective at a stalk is a monomorphism on some neighborhood. -/
@[stacks 01Y3 "(2)"]
#check (AlgebraicGeometry.Scheme.Modules.IsCoherent.existsNeighborhood_mono_of_injective :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
      (φ : G ⟶ F) (x : X)
      (_ : Function.Injective (RingedSpace.moduleStalkMap x φ)),
    ∃ (U : X.Opens) (_ : x ∈ U), Mono (SheafOfModules.Hom.over φ U))

/- Lemma 30.9.5 (3) (01Y3): a morphism of coherent module sheaves on a locally Noetherian scheme
which is surjective at a stalk is an epimorphism on some neighborhood. -/
@[stacks 01Y3 "(3)"]
#check (AlgebraicGeometry.Scheme.Modules.IsCoherent.existsNeighborhood_epi_of_surjective :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
      (φ : G ⟶ F) (x : X)
      (_ : Function.Surjective (RingedSpace.moduleStalkMap x φ)),
    ∃ (U : X.Opens) (_ : x ∈ U), Epi (SheafOfModules.Hom.over φ U))

/- Lemma 30.9.5 (4) (01Y3): a morphism of coherent module sheaves on a locally Noetherian scheme
which is bijective at a stalk is an isomorphism on some neighborhood. -/
@[stacks 01Y3 "(4)"]
#check (AlgebraicGeometry.Scheme.Modules.IsCoherent.existsNeighborhood_isIso_of_bijective :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {G F : X.Modules} [G.IsCoherent] [F.IsCoherent]
      (φ : G ⟶ F) (x : X)
      (_ : Function.Bijective (RingedSpace.moduleStalkMap x φ)),
    ∃ (U : X.Opens) (_ : x ∈ U), IsIso (SheafOfModules.Hom.over φ U))
