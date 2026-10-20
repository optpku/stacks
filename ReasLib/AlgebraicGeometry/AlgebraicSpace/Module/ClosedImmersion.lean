module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealQuotient

/-!
# Module sheaves along closed immersions

Pushforward along a closed immersion is exact, its adjunction counit is
invertible, and the adjunction unit identifies a module modulo the defining
ideal action with its pullback followed by pushforward.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S}

/-- Pushforward of module sheaves along a closed immersion of algebraic spaces is exact. -/
theorem Modules.pushforward_exact (i : Z ⟶ X) [IsClosedImmersion i] :
    exactFunctor Z.Modules X.Modules (Modules.pushforward i) :=
  sorry

/-- For a closed immersion of algebraic spaces, the adjunction unit induces an
isomorphism from every module modulo the defining ideal action to its pullback
followed by pushforward. -/
@[instance]
theorem IsClosedImmersion.isIso_quotientByIdealComparison (i : Z ⟶ X)
    [IsClosedImmersion i] (F : X.Modules) :
    IsIso (Modules.quotientByIdealComparison i F) :=
  sorry

/-- The pullback-pushforward adjunction counit for a closed immersion of algebraic
spaces is an isomorphism on every module sheaf. -/
@[instance]
theorem IsClosedImmersion.isIso_modulesAdjunction_counit (i : Z ⟶ X)
    [IsClosedImmersion i] :
    IsIso (Modules.pullbackPushforwardAdjunction i).counit :=
  sorry

namespace Modules

/-- Two quasi-coherent modules on a closed subspace with chosen pushforward
identifications to `F` admit a unique isomorphism compatible with those
identifications. -/
theorem existsUnique_iso_of_pushforward_iso {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} {F : X.Modules} (i : Z ⟶ X) [IsClosedImmersion i]
    (G G' : Z.Modules) [G.IsQuasicoherent] [G'.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F) (e' : (pushforward i).obj G' ≅ F) :
    ∃! α : G ≅ G', ((pushforward i).mapIso α).trans e' = e :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace
