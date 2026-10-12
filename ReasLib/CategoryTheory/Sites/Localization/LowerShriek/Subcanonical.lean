/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Over.LeftKanExtension
public import ReasLib.CategoryTheory.Sites.Localization.LowerShriek.AssociatedSheaf

@[expose] public section

open CategoryTheory Opposite

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Localization.LowerShriek.Subcanonical

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) [J.Subcanonical] (U : C)

/-- For a subcanonical topology, the left Kan extension of a sheaf on `C / U` is already a sheaf
on `C`.  This raw-presheaf form is the reusable core of Lemma 7.27.1. -/
theorem isSheaf_lan
    (G : (Over U)ᵒᵖ ⥤ Type (max u v))
    (hG : Presieve.IsSheaf (J.over U) G) :
    Presheaf.IsSheaf J ((Over.forget U).op.lan.obj G) := sorry

/-- The underlying presheaf of localization lower shriek is canonically the left Kan extension
along `(Over.forget U).op` when `J` is subcanonical. -/
noncomputable def underlyingIsoLan
    (G : Sheaf (J.over U) (Type (max u v))) :
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj G).obj ≅
      (Over.forget U).op.lan.obj G.obj :=
  (sheafToPresheaf J (Type (max u v))).mapIso <|
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).mapIso
        (sheafificationIso G)) ≪≫
      localization_lowerShriek_associatedSheafIso J U G.obj ≪≫
        (sheafificationIso
          ⟨(Over.forget U).op.lan.obj G.obj,
            isSheaf_lan J U G.obj
              ((isSheaf_iff_isSheaf_of_type (J.over U) G.obj).1 G.property)⟩).symm

/-- Lemma 7.27.1 (03HT): for a subcanonical site, evaluating localization lower shriek at `V`
is the sigma type of sections of `G` indexed by morphisms `V ⟶ U`. -/
@[stacks 03HT]
noncomputable def objIsoSigma
    (G : Sheaf (J.over U) (Type (max u v))) (V : C) :
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj G).obj.obj (op V) ≅
      Σ φ : V ⟶ U, G.obj.obj (op (Over.mk φ)) :=
  (underlyingIsoLan J U G).app (op V) ≪≫
    Over.Forget.LeftKanExtension.objIsoSigma U G.obj V

/-- The fiber of the subcanonical lower-shriek sigma chart over a map `φ : V ⟶ U` is the
corresponding value of the input sheaf on `Over.mk φ`. -/
noncomputable def fiberIsoMk
    (G : Sheaf (J.over U) (Type (max u v))) {V : C} (φ : V ⟶ U) :
    {s : (((Over.forget U).sheafPullback
        (Type (max u v)) (J.over U) J).obj G).obj.obj (op V) //
      ((objIsoSigma J U G V).hom s).1 = φ} ≅
      G.obj.obj (op (Over.mk φ)) :=
  ((Equiv.subtypeEquiv (objIsoSigma J U G V).toEquiv (fun _ ↦ Iff.rfl)).trans
    (Equiv.sigmaSubtype φ)).toIso

/-- The fiber of the subcanonical lower-shriek sigma chart over a slice object is its value on
that object. -/
noncomputable def fiberIso
    (G : Sheaf (J.over U) (Type (max u v))) (X : Over U) :
    {s : (((Over.forget U).sheafPullback
        (Type (max u v)) (J.over U) J).obj G).obj.obj (op X.left) //
      ((objIsoSigma J U G X.left).hom s).1 = X.hom} ≅
      G.obj.obj (op X) :=
  fiberIsoMk J U G X.hom

/-- The subcanonical fiber equivalence reads the second sigma coordinate, up to the dependent
transport determined by its first-coordinate equality. -/
theorem fiberIso.hom_heq_snd
    (G : Sheaf (J.over U) (Type (max u v))) (X : Over U)
    (s : (((Over.forget U).sheafPullback
      (Type (max u v)) (J.over U) J).obj G).obj.obj (op X.left))
    (hs : ((objIsoSigma J U G X.left).hom s).1 = X.hom) :
    HEq ((fiberIso J U G X).hom ⟨s, hs⟩)
      ((objIsoSigma J U G X.left).hom s).2 := sorry

/-- The inverse subcanonical sigma chart is the raw left-Kan-extension unit generator transported
back through the underlying-presheaf comparison. -/
@[simp]
theorem objIsoSigma.inv_mk
    (G : Sheaf (J.over U) (Type (max u v))) {V : C}
    (a : V ⟶ U) (s : G.obj.obj (op (Over.mk a))) :
    (objIsoSigma J U G V).inv ⟨a, s⟩ =
      (underlyingIsoLan J U G).inv.app (op V)
        (((Over.forget U).op.leftKanExtensionUnit G.obj).app
          (op (Over.mk a)) s) := sorry

/-- The inverse fiber chart has the expected underlying transported unit generator. -/
@[simp]
theorem fiberIsoMk.inv_val
    (G : Sheaf (J.over U) (Type (max u v))) {V : C}
    (a : V ⟶ U) (s : G.obj.obj (op (Over.mk a))) :
    ((fiberIsoMk J U G a).inv s).1 =
      (underlyingIsoLan J U G).inv.app (op V)
        (((Over.forget U).op.leftKanExtensionUnit G.obj).app
          (op (Over.mk a)) s) := sorry

/-- At a slice object, the inverse fiber chart has the expected underlying transported unit
generator. -/
@[simp]
theorem fiberIso.inv_val
    (G : Sheaf (J.over U) (Type (max u v)))
    (X : Over U) (s : G.obj.obj (op X)) :
    ((fiberIso J U G X).inv s).1 =
      (underlyingIsoLan J U G).inv.app (op X.left)
        (((Over.forget U).op.leftKanExtensionUnit G.obj).app
          (op X) s) := sorry

/-- In the subcanonical sigma chart, restriction postcomposes the indexing map and applies the
input sheaf to the induced morphism in `Over U`. -/
theorem objIsoSigma.hom_map
    (G : Sheaf (J.over U) (Type (max u v))) {V Y : C}
    (f : Y ⟶ V)
    (x : (((Over.forget U).sheafPullback
      (Type (max u v)) (J.over U) J).obj G).obj.obj (op V)) :
    (objIsoSigma J U G Y).hom
        ((((Over.forget U).sheafPullback
          (Type (max u v)) (J.over U) J).obj G).obj.map f.op x) =
      ⟨f ≫ ((objIsoSigma J U G V).hom x).1,
        G.obj.map
          (Over.homMk f :
            Over.mk (f ≫ ((objIsoSigma J U G V).hom x).1) ⟶
              Over.mk ((objIsoSigma J U G V).hom x).1).op
          ((objIsoSigma J U G V).hom x).2⟩ := sorry

end CategoryTheory.GrothendieckTopology.Localization.LowerShriek.Subcanonical
