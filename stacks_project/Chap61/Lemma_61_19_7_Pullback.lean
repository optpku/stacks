/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Torsor
public import stacks_project.Chap61.Lemma_61_19_1_Comparison

/-!
# Pullback of étale torsors along `etaleToProEt`

Objectwise inverse image of a `G`-torsor on `X.Etale` along the étale-to-pro-étale
comparison, together with the induced map on `Torsor.IsoClasses`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})
variable [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt X).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ GrpCat.{u + 1}, (etaleToProEt X).op.HasLeftKanExtension P]
variable [HasWeakSheafify (ProEt.topology X) (Type (u + 1))]
variable [HasWeakSheafify (ProEt.topology X) GrpCat.{u + 1}]
variable [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget GrpCat.{u + 1})]
variable [(ProEt.topology X).HasSheafCompose (CategoryTheory.forget GrpCat.{u + 1})]
variable [(CategoryTheory.forget GrpCat.{u + 1}).PreservesLeftKanExtensions (etaleToProEt X).op]
variable [(ProEt.topology X).PreservesSheafification (CategoryTheory.forget GrpCat.{u + 1})]
variable [PreservesFiniteLimits (etaleToProEtPullback X (Type (u + 1)))]

/-- The action of a group sheaf on a torsor, as a morphism of sheaves of types. -/
def etaleToProEtTorsor_sourceAction
    {G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}} (P : Torsor G) :
    (sheafForget X.smallEtaleTopology).obj G ⨯ P.carrier ⟶ P.carrier :=
  Sheaf.homEquiv.symm
    { app := fun U ↦
        TypeCat.ofHom fun p ↦
          (P.mulAction U.unop).smul
            ((prod.fst :
                (sheafForget X.smallEtaleTopology).obj G ⨯ P.carrier ⟶
                  (sheafForget X.smallEtaleTopology).obj G).hom.app U p)
            ((prod.snd :
                (sheafForget X.smallEtaleTopology).obj G ⨯ P.carrier ⟶
                  P.carrier).hom.app U p)
      naturality := sorry }

/-- Forgetting groups commutes with inverse image along `etaleToProEt`. -/
def etaleToProEtPullback_forgetGrp
    (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) :
    (sheafForget (ProEt.topology X)).obj
        ((etaleToProEtPullback X GrpCat.{u + 1}).obj G) ≅
      (etaleToProEtPullback X (Type (u + 1))).obj
        ((sheafForget X.smallEtaleTopology).obj G) :=
  (Functor.sheafPullback.compSheafComposeIso (etaleToProEt X) (CategoryTheory.forget GrpCat.{u + 1})
    X.smallEtaleTopology (ProEt.topology X)).app G

/-- The pulled-back action of `ε⁻¹ G` on `ε⁻¹ P`, as a morphism of sheaves of types
on `X.ProEt`. -/
def etaleToProEtTorsor_action
    (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) (P : Torsor G) :
    (sheafForget (ProEt.topology X)).obj
          ((etaleToProEtPullback X GrpCat.{u + 1}).obj G) ⨯
        (etaleToProEtPullback X (Type (u + 1))).obj P.carrier ⟶
      (etaleToProEtPullback X (Type (u + 1))).obj P.carrier :=
  prod.map (etaleToProEtPullback_forgetGrp X G).hom (𝟙 _) ≫
    (PreservesLimitPair.iso (etaleToProEtPullback X (Type (u + 1)))
        ((sheafForget X.smallEtaleTopology).obj G) P.carrier).inv ≫
      (etaleToProEtPullback X (Type (u + 1))).map (etaleToProEtTorsor_sourceAction X P)

/-- Assemble a section of a binary product of type-valued sheaves on `X.ProEt`. -/
def proEtTypeSheafProdSection
    (A B : Sheaf (ProEt.topology X) (Type (u + 1))) {U : X.ProEtᵒᵖ}
    (a : A.obj.obj U) (b : B.obj.obj U) : (A ⨯ B).obj.obj U :=
  (PreservesLimitPair.iso (sheafToPresheaf (ProEt.topology X) (Type (u + 1))) A B).inv.app U
    (FunctorToTypes.prodMk a b)

/-- Objectwise scalar multiplication of the pulled-back torsor. -/
def etaleToProEtTorsor_smul
    (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) (P : Torsor G) (U : X.ProEt)
    (g : ((etaleToProEtPullback X GrpCat.{u + 1}).obj G).obj.obj (op U))
    (x : ((etaleToProEtPullback X (Type (u + 1))).obj P.carrier).obj.obj (op U)) :
    ((etaleToProEtPullback X (Type (u + 1))).obj P.carrier).obj.obj (op U) :=
  (etaleToProEtTorsor_action X G P).hom.app (op U)
    (proEtTypeSheafProdSection X
      ((sheafForget (ProEt.topology X)).obj ((etaleToProEtPullback X GrpCat.{u + 1}).obj G))
      ((etaleToProEtPullback X (Type (u + 1))).obj P.carrier) g x)

/-- Inverse image of a `G`-torsor on `X.Etale` along `etaleToProEt`. -/
def etaleToProEtTorsor
    (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) (P : Torsor G) :
    Torsor ((etaleToProEtPullback X GrpCat.{u + 1}).obj G) where
  carrier := (etaleToProEtPullback X (Type (u + 1))).obj P.carrier
  mulAction U :=
    { smul := etaleToProEtTorsor_smul X G P U
      one_smul := sorry
      mul_smul := sorry }
  act_naturality := sorry
  isPretransitive := sorry
  isCancelSMul := sorry
  locallyNonempty := sorry

/-- The underlying sheaf of sets of `etaleToProEtTorsor G P` is `ε⁻¹` of the
underlying sheaf of `P`. -/
theorem etaleToProEtTorsor_carrier
    (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) (P : Torsor G) :
    (etaleToProEtTorsor X G P).carrier =
      (etaleToProEtPullback X (Type (u + 1))).obj P.carrier :=
  sorry

/-- Inverse image of an equivariant morphism of étale torsors along `etaleToProEt`. -/
def etaleToProEtTorsor_map
    {G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}} {P Q : Torsor G} (f : Torsor.Hom P Q) :
    Torsor.Hom (etaleToProEtTorsor X G P) (etaleToProEtTorsor X G Q) where
  hom := (etaleToProEtPullback X (Type (u + 1))).map f.hom
  comm := sorry

/-- The canonical comparison of torsor isomorphism classes along `etaleToProEt`. -/
def etaleToProEt_torsorIsoClasses (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) :
    Torsor.IsoClasses G →
      Torsor.IsoClasses ((etaleToProEtPullback X GrpCat.{u + 1}).obj G) :=
  Quotient.lift (fun P ↦ Quotient.mk'' (etaleToProEtTorsor X G P)) fun _ _ _ ↦ sorry

/-- The comparison of torsor classes applies as inverse image on representatives. -/
theorem etaleToProEt_torsorIsoClasses_mk
    (G : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) (P : Torsor G) :
    etaleToProEt_torsorIsoClasses X G (Quotient.mk'' P) =
      Quotient.mk'' (etaleToProEtTorsor X G P) :=
  sorry

end AlgebraicGeometry.Scheme
