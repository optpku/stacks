/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback.Hom
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Functoriality
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-!
# Open immersions of groupoid-scheme quotient sheaves

An open saturation image with a locally surjective corestriction induces an open immersion on
the associated quotient sheaves.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- An open saturation image with a locally surjective corestriction induces a representable
open immersion between the corresponding fppf quotient sheaves. -/
theorem pullbackQuotientMap_isOpenImmersion {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.U) (W : G.U.left.Opens)
    (hToImage : Limits.pullback g G.t ⟶ Over.mk (W.ι ≫ G.U.hom))
    (h_range : Set.range (((Limits.pullback.snd g G.t) ≫ G.s).left.base) =
      (W : Set G.U.left))
    (h_factor : hToImage.left ≫ W.ι = ((Limits.pullback.snd g G.t) ≫ G.s).left)
    (h_surj : Sheaf.IsLocallySurjective
      ((Scheme.fppfTopology.over S).uliftSheafifiedRepresentableMap.{u + 1} hToImage)) :
    (MorphismProperty.over (@IsOpenImmersion)).relative uliftYoneda.{u + 1}
      ((G.toPreRelation.pullbackHom g).quotientSheafMap (Scheme.fppfTopology.over S)).hom := sorry

end AlgebraicGeometry.GroupoidScheme
