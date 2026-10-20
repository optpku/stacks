module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.QuotientMap
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Minimality
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

/-!
# Rigidity of minimal smooth prorepresentable quotients

Every autoequivalence over the base of the quotient of a minimal smooth
prorepresentable groupoid is strictly invertible.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Every autoequivalence over the base of the quotient of a minimal smooth
prorepresentable groupoid in functors is an isomorphism. -/
theorem isIso_of_isEquivalence
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    (φ : BasedCategory.ofFunctor G.forget ⟶ BasedCategory.ofFunctor G.forget)
    [BasedFunctor.IsEquivalence φ] :
    IsIso φ := sorry

/-- If an endomorphism of a minimal smooth prorepresentable groupoid in functors
induces an autoequivalence of its quotient, its object-functor component is an isomorphism. -/
theorem Hom.isIso_obj_of_isEquivalence
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G] (f : Hom G G)
    [BasedFunctor.IsEquivalence (toQuotientBasedFunctor f)] :
    IsIso f.obj := sorry

/-- If an endomorphism of a minimal smooth prorepresentable groupoid in functors
induces an autoequivalence of its quotient, its arrow-functor component is an isomorphism. -/
theorem Hom.isIso_arrow_of_isEquivalence
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G] (f : Hom G G)
    [BasedFunctor.IsEquivalence (toQuotientBasedFunctor f)] :
    IsIso f.arrow := sorry

/-- Every equivalence over the base between the quotients of two minimal smooth
prorepresentable groupoids in functors is an isomorphism. -/
theorem isIso_of_isEquivalence_between
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H]
    (φ : BasedCategory.ofFunctor G.forget ⟶ BasedCategory.ofFunctor H.forget)
    [BasedFunctor.IsEquivalence φ] :
    IsIso φ := sorry

/-- If a morphism of minimal smooth prorepresentable groupoids in functors
induces an equivalence of quotients, then the object-functor component is an
isomorphism. -/
theorem Hom.isIso_obj_of_isEquivalence_between
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H] (f : Hom G H)
    [BasedFunctor.IsEquivalence (toQuotientBasedFunctor f)] :
    IsIso f.obj := sorry

/-- If a morphism of minimal smooth prorepresentable groupoids in functors
induces an equivalence of quotients, then the arrow-functor component is an
isomorphism. -/
theorem Hom.isIso_arrow_of_isEquivalence_between
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H] (f : Hom G H)
    [BasedFunctor.IsEquivalence (toQuotientBasedFunctor f)] :
    IsIso f.arrow := sorry

end CategoryTheory.GroupoidInFunctors
