module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.DegreeLocus

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Lemma 37.45.5 (1): the first open subscheme in the degree filtration is the whole base. -/
@[stacks 086R] #check
  (AlgebraicGeometry.Scheme.Hom.degreeAtLeastOpen_zero :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      [IsSeparated f] [LocallyQuasiFinite f],
      f.degreeAtLeastOpen 0 = ⊤)

/- Lemma 37.45.5 (2): the degree-at-least open subschemes form a decreasing sequence. -/
@[stacks 086R] #check
  (AlgebraicGeometry.Scheme.Hom.degreeAtLeastOpen_antitone :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      [IsSeparated f] [LocallyQuasiFinite f],
      Antitone f.degreeAtLeastOpen)

/- Lemma 37.45.5 (3): a field-valued point factors through the `d`th open exactly when its
pullback has degree at least `d`. -/
@[stacks 086R] #check
  (AlgebraicGeometry.Scheme.Hom.factorsThrough_degreeAtLeastOpen_iff :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      [IsSeparated f] [LocallyQuasiFinite f] {k : Type u} [Field k]
      (g : Spec (CommRingCat.of k) ⟶ S) (d : ℕ),
      (∃ lift : Spec (CommRingCat.of k) ⟶ (f.degreeAtLeastOpen d).toScheme,
        lift ≫ (f.degreeAtLeastOpen d).ι = g) ↔
        (pullback.snd f g).HasDegreeAtLeast d)

end Scheme.Hom
end AlgebraicGeometry
