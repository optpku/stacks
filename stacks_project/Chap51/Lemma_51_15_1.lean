module

public import ReasLib.AlgebraicGeometry.Scheme.Module.DepthOneQuotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 51.15.1 (1): a coherent module on a Noetherian scheme has a coherent depth-one
quotient along any subset stable under specialization. -/
@[stacks 0DX3] #check (AlgebraicGeometry.Scheme.Modules.IsDepthOneQuotient.«exists» :
  ∀ {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T) (F : X.Modules) [F.IsCoherent],
    ∃ (G : X.Modules) (_ : G.IsCoherent) (π : F ⟶ G), IsDepthOneQuotient T π)

/- Lemma 51.15.1 (2): two coherent depth-one quotients are related by a unique target
isomorphism compatible with their maps from the source. -/
@[stacks 0DX3]
#check (AlgebraicGeometry.Scheme.Modules.IsDepthOneQuotient.existsUniqueIso :
  ∀ {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F G H : X.Modules) [F.IsCoherent] [G.IsCoherent] [H.IsCoherent]
    (π : F ⟶ G) (ρ : F ⟶ H)
    (hπ : IsDepthOneQuotient T π) (hρ : IsDepthOneQuotient T ρ),
    ∃! e : G ≅ H, π ≫ e.hom = ρ)

/- Lemma 51.15.1 (3): flat pullback preserves the depth-one quotient property over the
inverse image of the specialization-stable subset. -/
@[stacks 0DX3]
#check (AlgebraicGeometry.Scheme.Modules.IsDepthOneQuotient.pullback_of_flat :
  ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent]
    (π : F ⟶ G) (hπ : IsDepthOneQuotient T π)
    (f : Y ⟶ X) [Flat f],
    IsDepthOneQuotient (f.base ⁻¹' T) ((pullback f).map π))

end AlgebraicGeometry.Scheme.Modules
