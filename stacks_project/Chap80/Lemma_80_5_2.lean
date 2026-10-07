module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap80.Definition_80_4_1_Relative

/-!
# Bootstrap of separated locally quasi-finite representability

A cartesian square of fppf sheaves on schemes over `S` with `g` representable
by algebraic spaces, surjective, flat, and locally of finite presentation, and
`a` representable by algebraic spaces, separated, and locally quasi-finite,
makes `b` representable by schemes, separated, and locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.5.2: let `S` be a scheme. Let `a : E ⟶ F`, `f : E ⟶ H`,
`g : F ⟶ G`, and `b : H ⟶ G` form a cartesian square of sheaves on
`(Sch/S)_fppf`, so `E = H ×_G F`. If `g` is representable by algebraic spaces,
surjective, flat, and locally of finite presentation, and `a` is representable
by algebraic spaces, separated, and locally quasi-finite, then `b` is
representable by schemes as well as separated and locally quasi-finite. -/
@[stacks 046J]
theorem separatedLocallyQuasiFinite_presheaf_of_isPullback
    {S : Scheme.{u}} {E F H G : (Over S)ᵒᵖ ⥤ Type u}
    {a : E ⟶ F} {f : E ⟶ H} {g : F ⟶ G} {b : H ⟶ G}
    (hE : Presheaf.IsSheaf (Scheme.fppfTopology.over S) E)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (sq : IsPullback f a b g)
    (hg : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) g)
    (ha : relativeAlgebraicSpaces
      (@Separated S ⊓ @LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) a) :
    (over (@AlgebraicGeometry.IsSeparated ⊓ @AlgebraicGeometry.LocallyOfFiniteType ⊓
        @AlgebraicGeometry.LocallyQuasiFinite :
      MorphismProperty Scheme.{u})).presheaf b :=
  sorry

/-- In this cartesian square of fppf sheaves, the morphism `b` is representable
by schemes. -/
theorem relativelyRepresentable_of_isPullback
    {S : Scheme.{u}} {E F H G : (Over S)ᵒᵖ ⥤ Type u}
    {a : E ⟶ F} {f : E ⟶ H} {g : F ⟶ G} {b : H ⟶ G}
    (hE : Presheaf.IsSheaf (Scheme.fppfTopology.over S) E)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (sq : IsPullback f a b g)
    (hg : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) g)
    (ha : relativeAlgebraicSpaces
      (@Separated S ⊓ @LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) a) :
    yoneda.relativelyRepresentable b :=
  sorry

/-- In the cartesian square of the bootstrap lemma, `b` is separated as a
representable morphism of sheaves. -/
theorem isSeparated_presheaf_of_isPullback
    {S : Scheme.{u}} {E F H G : (Over S)ᵒᵖ ⥤ Type u}
    {a : E ⟶ F} {f : E ⟶ H} {g : F ⟶ G} {b : H ⟶ G}
    (hE : Presheaf.IsSheaf (Scheme.fppfTopology.over S) E)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (sq : IsPullback f a b g)
    (hg : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) g)
    (ha : relativeAlgebraicSpaces
      (@Separated S ⊓ @LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) a) :
    (over (@AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u})).presheaf b :=
  sorry

/-- In the cartesian square of the bootstrap lemma, `b` is locally quasi-finite
as a representable morphism of sheaves, in the Stacks sense of locally of finite
type and locally quasi-finite. -/
theorem locallyQuasiFinite_presheaf_of_isPullback
    {S : Scheme.{u}} {E F H G : (Over S)ᵒᵖ ⥤ Type u}
    {a : E ⟶ F} {f : E ⟶ H} {g : F ⟶ G} {b : H ⟶ G}
    (hE : Presheaf.IsSheaf (Scheme.fppfTopology.over S) E)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (sq : IsPullback f a b g)
    (hg : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) g)
    (ha : relativeAlgebraicSpaces
      (@Separated S ⊓ @LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) a) :
    (over (@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite :
      MorphismProperty Scheme.{u})).presheaf b :=
  sorry

/-- For every scheme `T` over `S` and Yoneda section `ξ : yoneda.obj T ⟶ G`, the
structure morphism `T ×_G H ⟶ T` of the representing pullback of `b` along `ξ`
is separated, locally of finite type, and locally quasi-finite. -/
theorem separatedLocallyQuasiFinite_presheaf_of_isPullback_spec
    {S : Scheme.{u}} {E F H G : (Over S)ᵒᵖ ⥤ Type u}
    {a : E ⟶ F} {f : E ⟶ H} {g : F ⟶ G} {b : H ⟶ G}
    (hE : Presheaf.IsSheaf (Scheme.fppfTopology.over S) E)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (sq : IsPullback f a b g)
    (hg : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) g)
    (ha : relativeAlgebraicSpaces
      (@Separated S ⊓ @LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) a)
    {T : Over S} (ξ : yoneda.obj T ⟶ G) :
    (over (@AlgebraicGeometry.IsSeparated ⊓ @AlgebraicGeometry.LocallyOfFiniteType ⊓
        @AlgebraicGeometry.LocallyQuasiFinite :
      MorphismProperty Scheme.{u}))
      ((separatedLocallyQuasiFinite_presheaf_of_isPullback
          hE hF hH hG sq hg ha).rep.snd ξ) :=
  sorry

/-- The same conclusion when `E` is the canonical fibre product `H ×_G F`. -/
theorem separatedLocallyQuasiFinite_presheaf_of_hasPullback
    {S : Scheme.{u}} {F H G : (Over S)ᵒᵖ ⥤ Type u} {g : F ⟶ G} {b : H ⟶ G}
    [HasPullback b g]
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (hE : Presheaf.IsSheaf (Scheme.fppfTopology.over S) (pullback b g))
    (hg : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) g)
    (ha : relativeAlgebraicSpaces
      (@Separated S ⊓ @LocallyOfFiniteType S ⊓ @LocallyQuasiFinite S :
        MorphismProperty (AlgebraicSpace S)) (pullback.snd b g)) :
    (over (@AlgebraicGeometry.IsSeparated ⊓ @AlgebraicGeometry.LocallyOfFiniteType ⊓
        @AlgebraicGeometry.LocallyQuasiFinite :
      MorphismProperty Scheme.{u})).presheaf b :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
