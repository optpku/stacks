/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- In a cartesian square of fppf sheaves over a scheme, if the right morphism
is representable by algebraic spaces, surjective, flat, and locally of finite
presentation, and the top morphism is representable by algebraic spaces,
separated, locally of finite type, and locally quasi-finite, then the bottom
morphism is representable by schemes, separated, locally of finite type, and
locally quasi-finite. -/
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

end AlgebraicGeometry.AlgebraicSpace
