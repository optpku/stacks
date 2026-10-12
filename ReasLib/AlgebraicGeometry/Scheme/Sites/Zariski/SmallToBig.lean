/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Big
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.SheafEquivalence
public import Mathlib.Topology.Sheaves.Functors

/-!
# Small Zariski morphism relations

This leaf owns the cross-layer composition API for the small and big Zariski
topoi.  Its API lives directly below `Zariski.SmallToBig`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Zariski.SmallToBig

variable {S T : Scheme.{u}}

/-- The morphism of topoi induced by base change on small Zariski sites. -/
noncomputable def smallMorphism (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type (u + 1))] :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      S.smallZariskiTopology T.smallZariskiTopology :=
  IsMorphismOfSites.toMorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
    (smallZariskiPullback f)

/-- The small Zariski morphism is the one induced by the base-change functor of sites. -/
theorem smallMorphism_eq_induced (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type (u + 1))] :
    smallMorphism f =
      IsMorphismOfSites.toMorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
        (smallZariskiPullback f) := rfl

/-- Direct image for the induced small-Zariski morphism agrees, after the canonical sheaf
equivalences, with the usual direct image on the underlying topological spaces. -/
noncomputable def smallMorphism_pushforwardIsoUsual (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type (u + 1))] :
    (smallMorphism f) _* ⋙ (smallZariskiTypeSheafEquiv S).functor ≅
      (smallZariskiTypeSheafEquiv T).functor ⋙
        TopCat.Sheaf.pushforward (Type (u + 1)) f.base := by
  -- Local instance justification (defeq pin): the intermediate topology of this specific
  -- composite is not an input to typeclass search.
  letI : Functor.IsContinuous
      (TopologicalSpace.Opens.map (TopCat.ofHom f.base.hom) ⋙
        smallZariskiOpenFunctor T)
      (Opens.grothendieckTopology (S : TopCat)) T.smallZariskiTopology :=
    Functor.isContinuous_comp
      (TopologicalSpace.Opens.map (TopCat.ofHom f.base.hom))
      (smallZariskiOpenFunctor T) (Opens.grothendieckTopology (S : TopCat))
      (Opens.grothendieckTopology (T : TopCat)) T.smallZariskiTopology
  exact Functor.sheafPushforwardContinuousComp'
      (smallZariskiPullbackOpenFunctorIso f) (Type (u + 1))
      (Opens.grothendieckTopology (S : TopCat)) S.smallZariskiTopology
      T.smallZariskiTopology ≪≫
    (Functor.sheafPushforwardContinuousComp
      (TopologicalSpace.Opens.map (TopCat.ofHom f.base.hom))
      (smallZariskiOpenFunctor T) (Type (u + 1))
      (Opens.grothendieckTopology (S : TopCat))
      (Opens.grothendieckTopology (T : TopCat)) T.smallZariskiTopology).symm

/-- Inverse image for the induced small-Zariski morphism agrees, after the canonical sheaf
equivalences, with the usual inverse image on the underlying topological spaces. -/
noncomputable def smallMorphism_inverseImageIsoUsual (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type (u + 1))] :
    (smallMorphism f)⁻¹ ⋙ (smallZariskiTypeSheafEquiv T).functor ≅
      (smallZariskiTypeSheafEquiv S).functor ⋙
        (TopologicalSpace.Opens.map (TopCat.ofHom f.base.hom)).sheafPullback
          (Type (u + 1)) (Opens.grothendieckTopology (S : TopCat))
          (Opens.grothendieckTopology (T : TopCat)) :=
  Adjunction.leftAdjointUniq
    (((smallZariskiPullback f).sheafAdjunctionContinuous (Type (u + 1))
        S.smallZariskiTopology T.smallZariskiTopology).comp
      (smallZariskiTypeSheafEquiv T).toAdjunction |>.ofNatIsoRight
        (Iso.isoCompInverse (H := smallZariskiTypeSheafEquiv S)
          (Functor.associator (smallZariskiTypeSheafEquiv T).inverse
              ((smallZariskiPullback f).sheafPushforwardContinuous (Type (u + 1))
                S.smallZariskiTopology T.smallZariskiTopology)
              (smallZariskiTypeSheafEquiv S).functor ≪≫
            Iso.inverseCompIso (G := smallZariskiTypeSheafEquiv T)
              (smallMorphism_pushforwardIsoUsual f))))
    ((smallZariskiTypeSheafEquiv S).toAdjunction.comp
      ((TopologicalSpace.Opens.map (TopCat.ofHom f.base.hom)).sheafAdjunctionContinuous
        (Type (u + 1)) (Opens.grothendieckTopology (S : TopCat))
        (Opens.grothendieckTopology (T : TopCat))))

/-- Direct image along the induced small-Zariski morphism is computed by base change on
small-Zariski objects. -/
theorem smallMorphism_pushforward_obj_obj (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type (u + 1))]
    (ℱ : Sheaf T.smallZariskiTopology (Type (u + 1))) (U : S.smallZariskiSite) :
    (((smallMorphism f) _*).obj ℱ).1.obj (op U) =
      ℱ.1.obj (op ((smallZariskiPullback f).obj U)) := sorry

/-- The small-to-big Zariski morphism factors through the big Zariski morphism. -/
theorem morphism_eq_comp_big (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type (u + 1))] :
    morphismOfTopoi f =
      MorphismOfTopoiIn.comp
        (Zariski.Big.morphismOfTopoi f)
        (morphismOfTopoi (𝟙 T)) := sorry

/-- The square comparing small and big Zariski morphisms commutes. -/
theorem smallMorphism_comp_site (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type (u + 1))] :
    MorphismOfTopoiIn.comp
        (smallMorphism f)
        (siteMorphismOfTopoi T) =
      MorphismOfTopoiIn.comp
        (siteMorphismOfTopoi S)
        (Zariski.Big.morphismOfTopoi f) := sorry

/-- The small Zariski morphism has the expanded big-site factorization. -/
theorem smallMorphism_eq_comp_big (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type (u + 1))] :
    smallMorphism f =
      MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp
          (siteMorphismOfTopoi S)
          (Zariski.Big.morphismOfTopoi f))
        (morphismOfTopoi (𝟙 T)) := sorry

/-- The small Zariski morphism is the direct composite of the site morphism
with small-to-big relocalization. -/
theorem smallMorphism_eq_comp (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type (u + 1))] :
    smallMorphism f =
      MorphismOfTopoiIn.comp
        (siteMorphismOfTopoi S)
        (morphismOfTopoi f) := sorry

/-- Small Zariski morphisms of topoi compose along composition of scheme morphisms. -/
theorem smallMorphism_comp
    {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    MorphismOfTopoiIn.comp (smallMorphism g) (smallMorphism f) =
      smallMorphism (f ≫ g) := sorry

end AlgebraicGeometry.Scheme.Zariski.SmallToBig
