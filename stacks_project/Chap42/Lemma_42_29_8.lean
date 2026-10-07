module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Pushforward

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 42.29.8: Gysin pullback along the zero scheme of a section commutes with
proper pushforward from the corresponding pulled-back zero scheme. -/
@[stacks 02TA] #check (AlgebraicGeometry.Scheme.Modules.gysin_map_eq_map_gysin :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) [IsProper f.left] (ℒ : X.left.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ)
    (α' : CycleGroup X'.left (X'.hom.relativeDimensionFunction δ) (k + 1)),
    gysin X.hom δ ℒ s k
        (CycleGroup.mapHom f.left (X'.hom.relativeDimensionFunction δ)
          (X.hom.relativeDimensionFunction δ) (k + 1) α') =
      ChowGroup.map δ
        (Over.mk
          (zeroSchemeι ((pullback f.left).obj ℒ) (sectionsPullback f.left ℒ s) ≫ X'.hom))
        (Over.mk (zeroSchemeι ℒ s ≫ X.hom))
        (zeroSchemePullbackOverHom f ℒ s) k
        (gysin X'.hom δ ((pullback f.left).obj ℒ)
          (sectionsPullback f.left ℒ s) k α'))

end AlgebraicGeometry.Scheme.Modules
