module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.Scheme.representableMorphismProperty

/-- A representable morphism property descends along an fppf-locally-surjective
transformation when the underlying scheme-morphism property is stable under
base change and local at the target. -/
theorem of_pullback_fst {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {a : F ⟶ G} {b : H ⟶ G} [HasPullback b a]
    (ha : yoneda.relativelyRepresentable a)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) b)
    (ha' : representableMorphismProperty S P (pullback.fst b a)) :
    representableMorphismProperty S P a := sorry

/-- A representable morphism property is equivalent to the same property after
pullback along an fppf-locally-surjective transformation. -/
theorem pullback_fst_iff {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {a : F ⟶ G} {b : H ⟶ G} [HasPullback b a]
    (ha : yoneda.relativelyRepresentable a)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) b) :
    representableMorphismProperty S P (pullback.fst b a) ↔
      representableMorphismProperty S P a := by
  constructor
  · exact of_pullback_fst P ha h_surj
  · intro ha
    exact pullback_fst P a b ha

end AlgebraicGeometry.Scheme.representableMorphismProperty
