/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import stacks_project.Chap90.Definition_90_27_1
public import stacks_project.Chap90.Remark_90_21_2_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Autoequivalences of minimal smooth prorepresentable quotients

The quotient of a minimal smooth prorepresentable groupoid in functors on `C_Λ`
does not admit autoequivalences which are not automorphisms.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- The morphism of quotients `[U/R] ⟶ [U'/R']` over `ArtinianLocalAlgCat Λ k`
induced by a morphism of groupoids in functors. -/
def Hom.toQuotientBasedFunctor
    {G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)}
    (f : Hom G H) :
    BasedCategory.ofFunctor G.forget ⟶ BasedCategory.ofFunctor H.forget :=
  BasedFunctor.ofFunctor
    (Grothendieck.map (Functor.whiskerRight f.toNatTrans Grpd.forgetToCat))
    Grothendieck.functor_comp_forget

/-- The underlying functor of `toQuotientBasedFunctor f` is `Grothendieck.map` of
the associated natural transformation of fibre-groupoid functors. -/
theorem Hom.toQuotientBasedFunctor_toFunctor
    {G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)}
    (f : Hom G H) :
    (toQuotientBasedFunctor f).toFunctor =
      Grothendieck.map (Functor.whiskerRight f.toNatTrans Grpd.forgetToCat) :=
  sorry

/-- Lemma 90.27.4: let `(U, R, s, t, c)` be a minimal smooth prorepresentable
groupoid in functors on `ArtinianLocalAlgCat Λ k`. If
`φ : [U/R] ⟶ [U/R]` is an equivalence of categories cofibered in groupoids,
then `φ` is an isomorphism. -/
@[stacks 06KQ]
theorem isIso_of_isEquivalence
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    (φ : BasedCategory.ofFunctor G.forget ⟶ BasedCategory.ofFunctor G.forget)
    [BasedFunctor.IsEquivalence φ] :
    IsIso φ := sorry

/-- If an endomorphism of a minimal smooth prorepresentable groupoid in functors
induces an autoequivalence of `[U/R]`, then the object-functor component is an
isomorphism. -/
theorem Hom.isIso_obj_of_isEquivalence
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G] (f : Hom G G)
    [BasedFunctor.IsEquivalence (toQuotientBasedFunctor f)] :
    IsIso f.obj := sorry

/-- If an endomorphism of a minimal smooth prorepresentable groupoid in functors
induces an autoequivalence of `[U/R]`, then the arrow-functor component is an
isomorphism. -/
theorem Hom.isIso_arrow_of_isEquivalence
    (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G] (f : Hom G G)
    [BasedFunctor.IsEquivalence (toQuotientBasedFunctor f)] :
    IsIso f.arrow := sorry

end CategoryTheory.GroupoidInFunctors
