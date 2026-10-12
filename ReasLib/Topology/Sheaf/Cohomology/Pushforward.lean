/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.CategoryTheory.Sites.Cohomology.Map
public import ReasLib.Topology.Sheaf.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaf cohomology under a continuous map

This leaf owns the comparison maps on objectwise cohomology induced by inverse and direct image
of abelian sheaves.  The fundamental construction is the map on `Ext` induced by exact inverse
image.  Its source is identified using the canonical pullback isomorphism for sheafified free
abelian Yoneda objects.

For a general continuous map, direct-image cohomology on `U` need not agree with cohomology on
`f ⁻¹' U` in positive degree.  Accordingly, the reusable interface exposes a comparison map in
all degrees and records that this comparison is invertible in degree zero.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace TopCat
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace CategoryTheory.Sheaf

variable {X Y : TopCat.{u}}

section Pullback

/-- The map on cohomology over an open induced by inverse image along a continuous map.  It is
the map on `Ext` induced by exact pullback, precomposed with the canonical free abelian Yoneda
pullback isomorphism. -/
@[stacks 09V3 "pullback on cohomology over an open"]
noncomputable def pullbackCohomologyMap
    (f : X ⟶ Y) (G : Y.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    G.H' p U ⟶
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G).H' p ((Opens.map f).obj U) :=
  AddCommGrpCat.ofHom <|
    ((Ext.mk₀ (TopCat.Sheaf.FreeAbelianYoneda.pullbackIso f U).hom).precomp
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G) (zero_add p)).comp
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).mapExtAddHom
          (GrothendieckTopology.FreeAbelianYoneda.obj
            (Opens.grothendieckTopology Y) U) G p)

/-- Pullback on objectwise cohomology, bundled as a morphism of presheaves. -/
@[stacks 09V3 "pullback on the cohomology presheaf"]
noncomputable def pullbackCohomology
    (f : X ⟶ Y) (G : Y.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    G.cohomologyPresheaf p ⟶
      (Opens.map f).op ⋙
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G).cohomologyPresheaf p where
  app U := pullbackCohomologyMap f G p U.unop
  naturality := sorry

/-- The component of the pullback morphism of cohomology presheaves is
`pullbackCohomologyMap`. -/
theorem pullbackCohomology_app
    (f : X ⟶ Y) (G : Y.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    (pullbackCohomology f G p).app (op U) = pullbackCohomologyMap f G p U := sorry

/-- Pullback on cohomology commutes with restriction along an inclusion of opens. -/
theorem pullbackCohomologyMap_naturality
    (f : X ⟶ Y) (G : Y.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    {U V : Opens Y} (i : U ⟶ V) :
    (G.cohomologyPresheaf p).map i.op ≫ pullbackCohomologyMap f G p U =
      pullbackCohomologyMap f G p V ≫
        (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G).cohomologyPresheaf p).map
          ((Opens.map f).map i).op := sorry

/-- Pullback on cohomology is natural in the coefficient sheaf. -/
theorem pullbackCohomologyMap_map
    (f : X ⟶ Y) {G H : Y.Sheaf AddCommGrpCat.{u}} (g : G ⟶ H)
    (p : ℕ) (U : Opens Y) :
    cohomologyMap g p U ≫ pullbackCohomologyMap f H p U =
      pullbackCohomologyMap f G p U ≫
        cohomologyMap ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map g) p
          ((Opens.map f).obj U) := sorry

end Pullback

section Pushforward

/-- The canonical comparison from cohomology of a direct image over `U` to cohomology of the
original sheaf over `(Opens.map f).obj U`.  It is pullback on `Ext`, followed by the adjunction
counit on coefficients. -/
@[stacks 09V3 "pushforward cohomology comparison"]
noncomputable def pushforwardCohomologyMap
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).H' p U ⟶
      F.H' p ((Opens.map f).obj U) :=
  pullbackCohomologyMap f ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) p U ≫
    cohomologyMap
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).counit.app F) p
      ((Opens.map f).obj U)

/-- The defining factorization of the pushforward cohomology comparison. -/
theorem pushforwardCohomologyMap_def
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    pushforwardCohomologyMap f F p U =
      pullbackCohomologyMap f ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) p U ≫
        cohomologyMap
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).counit.app F) p
          ((Opens.map f).obj U) := sorry

/-- The direct-image comparison, bundled as a morphism of cohomology presheaves. -/
@[stacks 09V3 "pushforward cohomology comparison, presheaf form"]
noncomputable def pushforwardCohomology
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F).cohomologyPresheaf p ⟶
      (Opens.map f).op ⋙ F.cohomologyPresheaf p where
  app U := pushforwardCohomologyMap f F p U.unop
  naturality := sorry

/-- The component of the pushforward comparison of cohomology presheaves is
`pushforwardCohomologyMap`. -/
theorem pushforwardCohomology_app
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    (pushforwardCohomology f F p).app (op U) = pushforwardCohomologyMap f F p U := sorry

/-- If direct image along `f` is exact, its cohomology comparison over every open is an
isomorphism in every degree.  Exactness is an explicit hypothesis so this theorem also applies
beyond geometric closed embeddings. -/
@[stacks 02UV "exact direct-image comparison"]
theorem pushforwardCohomologyMap_isIso_of_exact
    (f : X ⟶ Y)
    (hf : exactFunctor (X.Sheaf AddCommGrpCat.{u}) (Y.Sheaf AddCommGrpCat.{u})
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    IsIso (pushforwardCohomologyMap f F p U) := sorry

/-- Pullback on cohomology factors through the adjunction unit and the direct-image
comparison. -/
@[stacks 09V3 "unit-comparison factorization"]
theorem cohomologyMap_unit_comp
    (f : X ⟶ Y) (G : Y.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Opens Y) :
    cohomologyMap
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app G) p U ≫
      pushforwardCohomologyMap f
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj G) p U =
      pullbackCohomologyMap f G p U := sorry

/-- In degree zero, direct-image cohomology over an open agrees with cohomology of the original
sheaf over the inverse-image open. -/
@[stacks 09V3 "degree-zero pushforward comparison"]
noncomputable instance pushforwardCohomologyMap_isIso_zero
    (f : X ⟶ Y) (F : X.Sheaf AddCommGrpCat.{u}) (U : Opens Y) :
    IsIso (pushforwardCohomologyMap f F 0 U) := sorry

end Pushforward

end CategoryTheory.Sheaf

/- Audit the core cohomology constructions. -/
