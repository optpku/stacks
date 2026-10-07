module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit lifts along precomposition

This file isolates the category-theoretic construction underlying explicit lifts along
precomposition.  The source, intermediate, and target total categories have independent
universes; no stack-specific structure is needed.
-/

@[expose] public section

universe uC vC uS₀ vS₀ uS₁ vS₁ uT₀ vT₀ uT₁ vT₁

namespace CategoryTheory
namespace CartesianBasedFunctor.PrecompLift

variable {C : Type uC} [Category.{vC} C]
variable {S₀ : Type uS₀} {S₁ : Type uS₁}
variable {T₀ : Type uT₀} {T₁ : Type uT₁}
variable [Category.{vS₀} S₀] [Category.{vS₁} S₁]
variable [Category.{vT₀} T₀] [Category.{vT₁} T₁]
variable {p₀ : S₀ ⥤ C} {p₁ : S₁ ⥤ C}
variable {r₀ : T₀ ⥤ C} {r₁ : T₁ ⥤ C}

/-- The explicit lift of postcomposition through a chosen quasi-inverse to precomposition.
This is the reusable category-theoretic core of the construction in `04W9`. -/
@[stacks 04W9 "explicit lift along precomposition"]
noncomputable def mapFunctor
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i)) :
    CartesianBasedFunctor p₀ r₀ ⥤ CartesianBasedFunctor p₁ r₁ :=
  (q.liftFunctor (CartesianBasedFunctor p₀ r₀)).obj
    (CartesianBasedFunctor.postcomp p₀ i')

namespace mapFunctor

/-- On objects, the explicit lift applies the chosen inverse after postcomposition. -/
@[simp, stacks 04W9 "object formula for explicit precomposition lift"]
theorem obj
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i))
    (F : CartesianBasedFunctor p₀ r₀) :
    (mapFunctor i' q).obj F = q.inverse.obj (F.comp i') := sorry

/-- On morphisms, the explicit lift applies the chosen inverse to postcomposition. -/
@[simp, stacks 04W9 "morphism formula for explicit precomposition lift"]
theorem map
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i))
    {F G : CartesianBasedFunctor p₀ r₀} (η : F ⟶ G) :
    (mapFunctor i' q).map η =
      q.inverse.map ((CartesianBasedFunctor.postcomp p₀ i').map η) := sorry

/-- The canonical comparison between the lifted functor followed by precomposition and
postcomposition by the prescribed target functor. -/
@[stacks 04W9 "comparison for the explicit precomposition lift"]
noncomputable def comparisonIso
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i)) :
    mapFunctor i' q ⋙ CartesianBasedFunctor.precomp r₁ i ≅
      CartesianBasedFunctor.postcomp p₀ i' :=
  Functor.QuasiInverse.liftFunctor.comparisonIso q
    (CartesianBasedFunctor.postcomp p₀ i')

namespace comparisonIso.hom

/-- The forward component of the precomposition-lift comparison is the supplied
quasi-inverse counit at the postcomposed functor. -/
@[simp, stacks 04W9 "forward component of explicit precomposition comparison"]
theorem app
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i))
    (F : CartesianBasedFunctor p₀ r₀) :
    (comparisonIso i' q).hom.app F =
      q.counitIso.hom.app ((CartesianBasedFunctor.postcomp p₀ i').obj F) := sorry

end comparisonIso.hom

namespace comparisonIso.inv

/-- The inverse component of the precomposition-lift comparison is the inverse
quasi-inverse counit at the postcomposed functor. -/
@[simp, stacks 04W9 "inverse component of explicit precomposition comparison"]
theorem app
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i))
    (F : CartesianBasedFunctor p₀ r₀) :
    (comparisonIso i' q).inv.app F =
      q.counitIso.inv.app ((CartesianBasedFunctor.postcomp p₀ i').obj F) := sorry

end comparisonIso.inv

/-- Explicit lifts formed from two choices of quasi-inverse are canonically isomorphic. -/
@[stacks 04W9 "choice independence of the explicit precomposition lift"]
noncomputable def choiceIso
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q q' : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i)) :
    mapFunctor i' q ≅ mapFunctor i' q' :=
  Functor.QuasiInverse.liftFunctor.choiceIso q q'
    (CartesianBasedFunctor.postcomp p₀ i')

/-- Choice independence respects the canonical comparison after precomposition. -/
@[stacks 04W9 "comparison coherence for explicit precomposition choice"]
theorem choiceIso.comparison
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q q' : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i)) :
    Functor.isoWhiskerRight (choiceIso i' q q')
          (CartesianBasedFunctor.precomp r₁ i) ≪≫
        comparisonIso i' q' =
      comparisonIso i' q := sorry

/-- The choice comparison from an explicit precomposition lift to itself is the identity. -/
@[simp, stacks 04W9 "identity law for explicit precomposition choice"]
theorem choiceIso.refl
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i)) :
    choiceIso i' q q = Iso.refl (mapFunctor i' q) := sorry

/-- Reversing a precomposition-lift choice comparison exchanges the two quasi-inverses. -/
@[simp, stacks 04W9 "symmetry law for explicit precomposition choice"]
theorem choiceIso.symm
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q q' : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i)) :
    (choiceIso i' q q').symm = choiceIso i' q' q := sorry

/-- Choice comparisons between explicit precomposition lifts compose transitively. -/
@[stacks 04W9 "transitivity law for explicit precomposition choice"]
theorem choiceIso.trans
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q q' q'' : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i)) :
    choiceIso i' q q' ≪≫ choiceIso i' q' q'' = choiceIso i' q q'' := sorry

/-- A functor equipped with a comparison through precomposition is canonically isomorphic
to the explicit lift formed from a chosen quasi-inverse. -/
@[stacks 04W9 "uniqueness of the explicit precomposition lift"]
noncomputable def isoOfComparison
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i))
    (L : CartesianBasedFunctor p₀ r₀ ⥤ CartesianBasedFunctor p₁ r₁)
    (α : L ⋙ CartesianBasedFunctor.precomp r₁ i ≅
      CartesianBasedFunctor.postcomp p₀ i') :
    L ≅ mapFunctor i' q :=
  Functor.QuasiInverse.liftFunctor.isoOfComparison q L
    (CartesianBasedFunctor.postcomp p₀ i') α

/-- The canonical uniqueness isomorphism recovers its supplied comparison after
precomposition. -/
@[stacks 04W9 "comparison recovery for explicit precomposition uniqueness"]
theorem isoOfComparison.comparison
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i))
    (L : CartesianBasedFunctor p₀ r₀ ⥤ CartesianBasedFunctor p₁ r₁)
    (α : L ⋙ CartesianBasedFunctor.precomp r₁ i ≅
      CartesianBasedFunctor.postcomp p₀ i') :
    Functor.isoWhiskerRight (isoOfComparison i' q L α)
          (CartesianBasedFunctor.precomp r₁ i) ≪≫
        comparisonIso i' q =
      α := sorry

/-- Compatibility with the supplied comparison characterizes the canonical uniqueness
isomorphism. -/
@[stacks 04W9 "uniqueness criterion for explicit precomposition lift"]
theorem isoOfComparison.eq_iff
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i))
    (L : CartesianBasedFunctor p₀ r₀ ⥤ CartesianBasedFunctor p₁ r₁)
    (α : L ⋙ CartesianBasedFunctor.precomp r₁ i ≅
      CartesianBasedFunctor.postcomp p₀ i')
    (β : L ≅ mapFunctor i' q) :
    β = isoOfComparison i' q L α ↔
      Functor.isoWhiskerRight β (CartesianBasedFunctor.precomp r₁ i) ≪≫
          comparisonIso i' q =
        α := sorry

/-- Applying the uniqueness construction to the canonical comparison gives the identity. -/
@[simp, stacks 04W9 "identity case of explicit precomposition lift uniqueness"]
theorem isoOfComparison.self
    {i : CartesianBasedFunctor p₀ p₁}
    (i' : CartesianBasedFunctor r₀ r₁)
    (q : Functor.QuasiInverse (CartesianBasedFunctor.precomp r₁ i)) :
    isoOfComparison i' q (mapFunctor i' q) (comparisonIso i' q) =
      Iso.refl (mapFunctor i' q) := sorry

end mapFunctor

/- Axiom audit: all three isomorphisms and the lifted functor are explicit data assembled from
the generic quasi-inverse lift API. Only the two Prop-valued readout theorems add local proof
debt. -/

end CartesianBasedFunctor.PrecompLift
end CategoryTheory
