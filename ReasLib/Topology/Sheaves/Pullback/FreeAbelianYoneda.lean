module

public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of sheafified free abelian Yoneda objects

This leaf owns the canonical comparison between pulling back the sheafified free abelian Yoneda
object of an open and the corresponding object of its inverse-image open. The comparison is
constructed from the common corepresented sections functor and is natural in the open.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace TopCat.Sheaf.FreeAbelianYoneda

variable {X Y : TopCat.{u}}

/-- Sections of abelian sheaves over an open, regarded as a type-valued functor. -/
noncomputable abbrev sections (X : TopCat.{u}) (U : Opens X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ Type u :=
  ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U)) ⋙
    CategoryTheory.forget AddCommGrpCat.{u}

/-- The sheafified free abelian Yoneda object corepresents sections over its open. -/
noncomputable def corep (X : TopCat.{u}) (U : Opens X) :
    (sections X U).CorepresentableBy
      (GrothendieckTopology.FreeAbelianYoneda.obj (Opens.grothendieckTopology X) U) where
  homEquiv {F} :=
    GrothendieckTopology.FreeAbelianYoneda.homEquiv
      (Opens.grothendieckTopology X) U F
  homEquiv_comp g a :=
    GrothendieckTopology.FreeAbelianYoneda.homEquiv_comp
      (Opens.grothendieckTopology X) U a g

/-- The adjunction identifies maps out of the pullback of a free abelian Yoneda object with
sections over the inverse-image open. -/
noncomputable def homEquiv (f : X ⟶ Y) (U : Opens Y) (F : X.Sheaf AddCommGrpCat.{u}) :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj
        (GrothendieckTopology.FreeAbelianYoneda.obj
          (Opens.grothendieckTopology Y) U) ⟶ F) ≃
      (sections X ((Opens.map f).obj U)).obj F :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).homEquiv _ _).trans
    (GrothendieckTopology.FreeAbelianYoneda.homEquiv
      (Opens.grothendieckTopology Y) U
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F))

/-- The pullback Hom/sections equivalence is natural in the target sheaf. -/
theorem homEquiv_comp (f : X ⟶ Y) (U : Opens Y)
    {F G : X.Sheaf AddCommGrpCat.{u}} (g : F ⟶ G)
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj
      (GrothendieckTopology.FreeAbelianYoneda.obj
        (Opens.grothendieckTopology Y) U) ⟶ F) :
    homEquiv f U G (a ≫ g) =
      (sections X ((Opens.map f).obj U)).map g (homEquiv f U F a) := sorry

/-- The pullback of the free abelian Yoneda object at `U` corepresents sections over
`(Opens.map f).obj U`. -/
noncomputable def pullbackCorep (f : X ⟶ Y) (U : Opens Y) :
    (sections X ((Opens.map f).obj U)).CorepresentableBy
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj
        (GrothendieckTopology.FreeAbelianYoneda.obj
          (Opens.grothendieckTopology Y) U)) where
  homEquiv {F} := homEquiv f U F
  homEquiv_comp g a := homEquiv_comp f U g a

/-- Pullback carries the sheafified free abelian Yoneda object at `U` to the corresponding
object at the inverse-image open. -/
@[stacks 09V3 "free abelian Yoneda pullback"]
noncomputable def pullbackIso (f : X ⟶ Y) (U : Opens Y) :
    GrothendieckTopology.FreeAbelianYoneda.obj
        (Opens.grothendieckTopology X) ((Opens.map f).obj U) ≅
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj
        (GrothendieckTopology.FreeAbelianYoneda.obj
          (Opens.grothendieckTopology Y) U) :=
  (corep X ((Opens.map f).obj U)).uniqueUpToIso (pullbackCorep f U)

/-- The free abelian Yoneda pullback isomorphisms commute with maps of opens. -/
theorem pullbackIso_naturality (f : X ⟶ Y) {U V : Opens Y} (i : U ⟶ V) :
    GrothendieckTopology.FreeAbelianYoneda.map
        (Opens.grothendieckTopology X) ((Opens.map f).map i) ≫
        (pullbackIso f V).hom =
      (pullbackIso f U).hom ≫
        (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map
          (GrothendieckTopology.FreeAbelianYoneda.map
            (Opens.grothendieckTopology Y) i) := sorry

/-- The pullback comparison for free abelian Yoneda objects, natural in the represented open. -/
@[stacks 09V3 "free abelian Yoneda pullback, natural form"]
noncomputable def pullbackNatIso (f : X ⟶ Y) :
    Opens.map f ⋙ GrothendieckTopology.FreeAbelianYoneda.functor
        (Opens.grothendieckTopology X) ≅
      GrothendieckTopology.FreeAbelianYoneda.functor
          (Opens.grothendieckTopology Y) ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{u} f :=
  NatIso.ofComponents (pullbackIso f) (fun i ↦ pullbackIso_naturality f i)

end TopCat.Sheaf.FreeAbelianYoneda

/- The comparison data is determined by the two corepresentations; deferred axioms occur only in
naturality and coherence proofs. -/
