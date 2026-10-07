module

public import stacks_project.Chap98.«98_3_0_2»
public import stacks_project.Chap98.Definition_98_5_1
public import stacks_project.Chap90.Definition_90_16_8
import Mathlib.Tactic.CrossRefAttribute

/-!
# Predeformation functors of Rim-Schlessinger groupoid fibrations

If `X` is a category fibred in groupoids over `(Sch/S)_{fppf}` satisfying (RS),
then the functor `p : ℱ_{X, k, x0} ⟶ ArtinianLocalAlgCat Λ k` of 98.3.0.2 is a
deformation category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

/-- Lemma 98.6.1: if `S` is locally Noetherian and `X` is a category fibred in
groupoids over `(Sch/S)_{fppf}` satisfying (RS), then for every finite-type field
`k` over `S` and every object `x0` of `X` over `Spec(k)`, the predeformation
functor `p : ℱ_{X, k, x0} ⥤ ArtinianLocalAlgCat Λ k` of 98.3.0.2 is a
deformation category. -/
@[stacks 07WU]
instance instIsDeformationCategory_predeformationFunctor
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (X : GroupoidsOver S) [HasRimSchlessinger X]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS)) :
    Functor.IsDeformationCategory
      (predeformationFunctor X openImmersion kToS h_factor x0) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
