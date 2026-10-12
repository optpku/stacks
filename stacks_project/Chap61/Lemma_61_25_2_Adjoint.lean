/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Functor.FreeAbelian
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelian
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom
public import stacks_project.Chap61.Lemma_61_12_21_Comparison
public import stacks_project.Chap61.Lemma_61_25_2_Comparison

/-!
# Lower shriek along an affine closed immersion

Left adjoints of inverse image on affine ind-étale sites are obtained by
sending weakly contractible representables `h_V` to `h_{v(V)}` (and `ℤ_V` to
`ℤ_{v(V)}`) and extending by colimits along that full subcategory of the
sheaf category. This is not presheaf left Kan extension along `v`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.ObjectProperty
open CostructuredArrow
open Opposite
open AlgebraicGeometry
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]

/-- Weakly contractible objects of the affine ind-étale site, as an object
property. -/
def AffineIndEtale.weaklyContractible (S : Scheme.{u}) [IsAffine S] :
    ObjectProperty (AffineIndEtale S) :=
  fun U ↦ (affineIndEtaleTopology S).IsWeaklyContractible U

/-- Weakly contractible objects are those for which the affine ind-étale
topology is weakly contractible. -/
theorem AffineIndEtale.weaklyContractible_iff (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    weaklyContractible S U ↔
      (affineIndEtaleTopology S).IsWeaklyContractible U :=
  sorry

/-- Objects of the weakly contractible full subcategory are weakly
contractible. -/
instance AffineIndEtale.weaklyContractible_obj
    (S : Scheme.{u}) [IsAffine S]
    (V : (weaklyContractible S).FullSubcategory) :
    (affineIndEtaleTopology S).IsWeaklyContractible V.obj :=
  V.property


/-- Sheafified Yoneda on weakly contractible affine ind-étale objects. -/
def AffineIndEtale.weaklyContractibleSheafifiedRepresentable
    (S : Scheme.{u}) [IsAffine S]
    [HasWeakSheafify (affineIndEtaleTopology S) (Type (u + 1))] :
    (weaklyContractible S).FullSubcategory ⥤
      Sheaf (affineIndEtaleTopology S) (Type (u + 1)) :=
  (weaklyContractible S).ι ⋙
    (affineIndEtaleTopology S).sheafifiedRepresentableFunctor

/-- Sheafified Yoneda on weakly contractible objects is inclusion followed by
sheafified representables. -/
theorem AffineIndEtale.weaklyContractibleSheafifiedRepresentable_def
    (S : Scheme.{u}) [IsAffine S]
    [HasWeakSheafify (affineIndEtaleTopology S) (Type (u + 1))] :
    weaklyContractibleSheafifiedRepresentable S =
      (weaklyContractible S).ι ⋙
        (affineIndEtaleTopology S).sheafifiedRepresentableFunctor :=
  sorry

/-- Weakly contractible sheafified representables generate the category of
type-valued sheaves on the affine ind-étale site. -/
instance AffineIndEtale.weaklyContractibleSheafifiedRepresentable_isDense
    (S : Scheme.{u}) [IsAffine S]
    [HasWeakSheafify (affineIndEtaleTopology S) (Type (u + 1))] :
    (weaklyContractibleSheafifiedRepresentable S).IsDense := sorry

/-- Sheafified Yoneda of the image of a weakly contractible object under the
affine ind-étale lift `v`. -/
def AffineIndEtale.weaklyContractibleLiftSheafifiedRepresentable
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))] :
    (weaklyContractible Z).FullSubcategory ⥤
      Sheaf (affineIndEtaleTopology X) (Type (u + 1)) :=
  (weaklyContractible Z).ι ⋙
    AffineIndEtale.lift i ⋙
    (affineIndEtaleTopology X).sheafifiedRepresentableFunctor

/-- The lift of weakly contractible sheafified representables is inclusion,
then `v`, then sheafified Yoneda. -/
theorem AffineIndEtale.weaklyContractibleLiftSheafifiedRepresentable_def
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))] :
    weaklyContractibleLiftSheafifiedRepresentable i =
      (weaklyContractible Z).ι ⋙
        AffineIndEtale.lift i ⋙
        (affineIndEtaleTopology X).sheafifiedRepresentableFunctor :=
  sorry

/-- Type-valued lower shriek along the affine ind-étale lift of a closed
immersion of affine schemes, as sheaf-category left Kan extension of
`h_V ↦ h_{v(V)}` on weakly contractible objects. -/
def AffineIndEtale.sheafLowerShriek (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)] :
    Sheaf (affineIndEtaleTopology Z) (Type (u + 1)) ⥤
      Sheaf (affineIndEtaleTopology X) (Type (u + 1)) :=
  (weaklyContractibleSheafifiedRepresentable Z).leftKanExtension
    (weaklyContractibleLiftSheafifiedRepresentable i)

/-- Type-valued lower shriek is sheaf-category left Kan extension of
`V ↦ h_{v(V)}` along weakly contractible sheafified representables. -/
theorem AffineIndEtale.sheafLowerShriek_def (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)] :
    sheafLowerShriek i =
      (weaklyContractibleSheafifiedRepresentable Z).leftKanExtension
        (weaklyContractibleLiftSheafifiedRepresentable i) :=
  sorry

/-- The Kan-extension unit component `h_{v(V)} ⟶ i^{Sh}_! h_V` is an
isomorphism on weakly contractible objects. -/
instance AffineIndEtale.sheafLowerShriek_leftKanExtensionUnit_app_isIso
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)]
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    IsIso
      (((weaklyContractibleSheafifiedRepresentable Z).leftKanExtensionUnit
          (weaklyContractibleLiftSheafifiedRepresentable i)).app
        ⟨V, ‹(affineIndEtaleTopology Z).IsWeaklyContractible V›⟩) :=
  sorry

/-- On a weakly contractible object, type-valued lower shriek sends the
sheafified representable `h_V` to `h_{v(V)}`. -/
def AffineIndEtale.sheafLowerShriek_obj_sheafifiedRepresentable
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)]
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    (sheafLowerShriek i).obj
        ((affineIndEtaleTopology Z).sheafifiedRepresentable V) ≅
      (affineIndEtaleTopology X).sheafifiedRepresentable
        ((AffineIndEtale.lift i).obj V) :=
  (asIso
      (((weaklyContractibleSheafifiedRepresentable Z).leftKanExtensionUnit
          (weaklyContractibleLiftSheafifiedRepresentable i)).app
        ⟨V, ‹(affineIndEtaleTopology Z).IsWeaklyContractible V›⟩)).symm

/-- The characterizing isomorphism of type-valued lower shriek on a weakly
contractible representable is the inverse Kan-extension unit. -/
theorem AffineIndEtale.sheafLowerShriek_obj_sheafifiedRepresentable_inv
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)]
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    (sheafLowerShriek_obj_sheafifiedRepresentable i V).inv =
      ((weaklyContractibleSheafifiedRepresentable Z).leftKanExtensionUnit
          (weaklyContractibleLiftSheafifiedRepresentable i)).app
        ⟨V, ‹(affineIndEtaleTopology Z).IsWeaklyContractible V›⟩ :=
  sorry

/-- Hom-equivalence `Hom(h_{v(V)}, G) ≃ Hom(h_V, i⁻¹ G)` on a weakly
contractible object. -/
def AffineIndEtale.sheafLowerShriekRepresentableHomEquiv
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    (V : (weaklyContractible Z).FullSubcategory)
    (G : Sheaf (affineIndEtaleTopology X) (Type (u + 1))) :
    ((affineIndEtaleTopology X).sheafifiedRepresentable
          ((AffineIndEtale.lift i).obj V.obj) ⟶
        G) ≃
      ((affineIndEtaleTopology Z).sheafifiedRepresentable V.obj ⟶
        ((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
            (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).obj G) :=
  ((affineIndEtaleTopology X).sheafifiedRepresentableHomEquiv G
        ((AffineIndEtale.lift i).obj V.obj)).trans <|
    (@asIso _ _ _ _
        (inverseImage_obj_to i G V.obj)
        (inverseImage_obj_to_isIso i G V.obj)).toEquiv.trans
      (((affineIndEtaleTopology Z).sheafifiedRepresentableHomEquiv
          (((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
              (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).obj G)
          V.obj).symm)

/-- Cocones of maps `h_{v(V)} ⟶ G` are equivalent to cocones of maps
`h_V ⟶ i⁻¹ G`. -/
def AffineIndEtale.sheafLowerShriekCoconeEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    (F : Sheaf (affineIndEtaleTopology Z) (Type (u + 1)))
    (G : Sheaf (affineIndEtaleTopology X) (Type (u + 1))) :
    { p :
          ∀ α : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F,
            (weaklyContractibleLiftSheafifiedRepresentable i).obj α.left ⟶ G //
        ∀ {α β : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F}
          (f : α ⟶ β),
          (weaklyContractibleLiftSheafifiedRepresentable i).map f.left ≫
              p β =
            p α } ≃
      { p :
          ∀ α : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F,
            (weaklyContractibleSheafifiedRepresentable Z).obj α.left ⟶
              ((AffineIndEtale.lift i).sheafPullbackCocontinuous
                  (Type (u + 1)) (affineIndEtaleTopology Z)
                  (affineIndEtaleTopology X)).obj G //
        ∀ {α β : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F}
          (f : α ⟶ β),
          (weaklyContractibleSheafifiedRepresentable Z).map f.left ≫ p β =
            p α } where
  toFun p :=
    ⟨fun α => sheafLowerShriekRepresentableHomEquiv i α.left G (p.1 α), sorry⟩
  invFun q :=
    ⟨fun α => (sheafLowerShriekRepresentableHomEquiv i α.left G).symm (q.1 α),
      sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- Morphisms out of the colimit of `h_{v(V)}` over a sheaf identify with
cocones of those maps. -/
def AffineIndEtale.sheafLowerShriekColimitHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)]
    (F : Sheaf (affineIndEtaleTopology Z) (Type (u + 1)))
    (G : Sheaf (affineIndEtaleTopology X) (Type (u + 1))) :
    (colimit
          (CostructuredArrow.proj
              (weaklyContractibleSheafifiedRepresentable Z) F ⋙
            weaklyContractibleLiftSheafifiedRepresentable i) ⟶
        G) ≃
      { p :
          ∀ α : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F,
            (weaklyContractibleLiftSheafifiedRepresentable i).obj α.left ⟶ G //
        ∀ {α β : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F}
          (f : α ⟶ β),
          (weaklyContractibleLiftSheafifiedRepresentable i).map f.left ≫
              p β =
            p α } :=
  Equiv.ulift.symm.trans
    (colimit.homIso'
        (CostructuredArrow.proj (weaklyContractibleSheafifiedRepresentable Z)
            F ⋙
          weaklyContractibleLiftSheafifiedRepresentable i)
        G).toEquiv

/-- Morphisms out of the colimit of `h_V` over a sheaf identify with cocones of
those maps. -/
def AffineIndEtale.sheafLowerShriekSourceColimitHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    (F : Sheaf (affineIndEtaleTopology Z) (Type (u + 1)))
    (G : Sheaf (affineIndEtaleTopology Z) (Type (u + 1))) :
    (colimit
          (CostructuredArrow.proj
              (weaklyContractibleSheafifiedRepresentable Z) F ⋙
            weaklyContractibleSheafifiedRepresentable Z) ⟶
        G) ≃
      { p :
          ∀ α : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F,
            (weaklyContractibleSheafifiedRepresentable Z).obj α.left ⟶ G //
        ∀ {α β : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F}
          (f : α ⟶ β),
          (weaklyContractibleSheafifiedRepresentable Z).map f.left ≫ p β =
            p α } :=
  Equiv.ulift.symm.trans
    (colimit.homIso'
        (CostructuredArrow.proj (weaklyContractibleSheafifiedRepresentable Z)
            F ⋙
          weaklyContractibleSheafifiedRepresentable Z)
        G).toEquiv

/-- Hom-equivalence exhibiting type-valued lower shriek as left adjoint of
inverse image along `v`. -/
def AffineIndEtale.sheafLowerShriekHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)]
    (F : Sheaf (affineIndEtaleTopology Z) (Type (u + 1)))
    (G : Sheaf (affineIndEtaleTopology X) (Type (u + 1))) :
    ((sheafLowerShriek i).obj F ⟶ G) ≃
      (F ⟶
        ((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
            (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).obj G) :=
  (((weaklyContractibleSheafifiedRepresentable Z).leftKanExtensionObjIsoColimit
            (weaklyContractibleLiftSheafifiedRepresentable i) F).homCongr
        (Iso.refl G)).trans <|
    (sheafLowerShriekColimitHomEquiv i F G).trans <|
      (sheafLowerShriekCoconeEquiv i F G).trans <|
        (sheafLowerShriekSourceColimitHomEquiv i F
              (((AffineIndEtale.lift i).sheafPullbackCocontinuous
                  (Type (u + 1)) (affineIndEtaleTopology Z)
                  (affineIndEtaleTopology X)).obj G)).symm.trans <|
          (((weaklyContractibleSheafifiedRepresentable Z).leftKanExtensionObjIsoColimit
                    (weaklyContractibleSheafifiedRepresentable Z)
                    F).symm.homCongr
                (Iso.refl
                  (((AffineIndEtale.lift i).sheafPullbackCocontinuous
                      (Type (u + 1)) (affineIndEtaleTopology Z)
                      (affineIndEtaleTopology X)).obj G))).trans
            (((IsDense.leftKanExtensionIso
                      (weaklyContractibleSheafifiedRepresentable Z)).app
                    F).homCongr
                (Iso.refl
                  (((AffineIndEtale.lift i).sheafPullbackCocontinuous
                      (Type (u + 1)) (affineIndEtaleTopology Z)
                      (affineIndEtaleTopology X)).obj G)))

/-- The packaged adjunction `i^{Sh}_! ⊣ i⁻¹` on type-valued sheaves, whose unit
is `id ⟶ i⁻¹ i^{Sh}_!`. -/
def AffineIndEtale.sheafLowerShriekAdjunction (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)] :
    sheafLowerShriek i ⊣
      (AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sheafLowerShriekHomEquiv i
      homEquiv_naturality_left_symm := fun _ _ => sorry
      homEquiv_naturality_right := fun _ _ => sorry }

/-- The unit of type-valued lower shriek is the unit of
`sheafLowerShriekAdjunction`. -/
theorem AffineIndEtale.sheafLowerShriekAdjunction_unit (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)]
    (F : Sheaf (affineIndEtaleTopology Z) (Type (u + 1))) :
    (sheafLowerShriekAdjunction i).unit.app F =
      (sheafLowerShriekHomEquiv i F
          ((sheafLowerShriek i).obj F)) (𝟙 _) :=
  sorry

/-- The unit `id ⟶ i⁻¹ i^{Sh}_!` is an isomorphism. -/
instance AffineIndEtale.sheafLowerShriek_unit_isIso (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)] :
    IsIso (sheafLowerShriekAdjunction i).unit := sorry

/-- Type-valued lower shriek is fully faithful, as its adjunction unit is an
isomorphism. -/
def AffineIndEtale.sheafLowerShriekFullyFaithful (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)] :
    (sheafLowerShriek i).FullyFaithful :=
  (sheafLowerShriekAdjunction i).fullyFaithfulLOfIsIsoUnit

/-- Free abelian sheaf represented by a weakly contractible affine object. -/
abbrev AffineIndEtale.weaklyContractibleFreeAbelianObj
    (S : Scheme.{u}) [IsAffine S]
    [HasWeakSheafify (affineIndEtaleTopology S) AddCommGrpCat.{u + 1}]
    (V : (weaklyContractible S).FullSubcategory) :
    Sheaf (affineIndEtaleTopology S) AddCommGrpCat.{u + 1} :=
  (affineIndEtaleTopology S).freeAbelianSheafFunctor.obj
    (uliftYoneda.{u + 1}.obj V.obj)

/-- Weakly contractible free abelian generators with ALL abelian sheaf morphisms.
The induced category retains additive relations, not just scheme reindexing maps. -/
abbrev AffineIndEtale.WeaklyContractibleAbelian
    (S : Scheme.{u}) [IsAffine S]
    [HasWeakSheafify (affineIndEtaleTopology S) AddCommGrpCat.{u + 1}] :=
  InducedCategory (Sheaf (affineIndEtaleTopology S) AddCommGrpCat.{u + 1})
    (weaklyContractibleFreeAbelianObj S)

/-- The fully faithful inclusion of these free generators into abelian sheaves. -/
def AffineIndEtale.weaklyContractibleFreeAbelian
    (S : Scheme.{u}) [IsAffine S]
    [HasWeakSheafify (affineIndEtaleTopology S) AddCommGrpCat.{u + 1}] :
    WeaklyContractibleAbelian S ⥤
      Sheaf (affineIndEtaleTopology S) AddCommGrpCat.{u + 1} :=
  inducedFunctor (weaklyContractibleFreeAbelianObj S)

/-- The inclusion uses the canonical induced-category functor. -/
theorem AffineIndEtale.weaklyContractibleFreeAbelian_def
    (S : Scheme.{u}) [IsAffine S]
    [HasWeakSheafify (affineIndEtaleTopology S) AddCommGrpCat.{u + 1}] :
    weaklyContractibleFreeAbelian S =
      inducedFunctor (weaklyContractibleFreeAbelianObj S) := rfl

/-- A morphism in the generator category is its specified abelian sheaf map. -/
theorem AffineIndEtale.weaklyContractibleFreeAbelian_map
    (S : Scheme.{u}) [IsAffine S]
    [HasWeakSheafify (affineIndEtaleTopology S) AddCommGrpCat.{u + 1}]
    {V W : WeaklyContractibleAbelian S} (f : V ⟶ W) :
    (weaklyContractibleFreeAbelian S).map f = f.hom := rfl

/-- The full free-generator subcategory is dense: weakly contractible covers
generate, and finite disjoint unions provide finite sums with all linear maps. -/
instance AffineIndEtale.weaklyContractibleFreeAbelian_isDense
    (S : Scheme.{u}) [IsAffine S]
    [HasWeakSheafify (affineIndEtaleTopology S) AddCommGrpCat.{u + 1}] :
    (weaklyContractibleFreeAbelian S).IsDense := sorry

/-- On a weakly contractible object, the sheafification unit of abelian
inverse image is an isomorphism. -/
instance AffineIndEtale.abelianInverseImage_sheafifyUnit_app_isIso
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    (F : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1})
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    IsIso
      (((sheafificationAdjunction (affineIndEtaleTopology Z)
          AddCommGrpCat.{u + 1}).unit.app
        ((AffineIndEtale.lift i).op ⋙ F.obj)).app (op V)) :=
  sorry

/-- Hom-equivalence `Hom(ℤ_{v(V)}, G) ≃ Hom(ℤ_V, i⁻¹ G)` on a weakly
contractible object. -/
def AffineIndEtale.abelianLowerShriekRepresentableHomEquiv
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    (V : (weaklyContractible Z).FullSubcategory)
    (G : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}) :
    ((affineIndEtaleTopology X).freeAbelianSheafFunctor.obj
          (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj)) ⟶
        G) ≃
      ((affineIndEtaleTopology Z).freeAbelianSheafFunctor.obj
          (uliftYoneda.{u + 1}.obj V.obj) ⟶
        (abelianInverseImage i).obj G) :=
  ((sheafificationAdjunction (affineIndEtaleTopology X)
          AddCommGrpCat.{u + 1}).homEquiv
        (FreeAbelianPresheaf.obj
          (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj)))
        G).trans <|
    (FreeAbelianPresheaf.homEquiv
          (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj))
          G.obj).trans <|
      ((uliftYonedaEquiv.{u + 1} :
            (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj) ⟶
              G.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) ≃
            (G.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).obj
              (op ((AffineIndEtale.lift i).obj V.obj)))).trans <|
        (asIso
            ((CategoryTheory.forget AddCommGrpCat.{u + 1}).map
              (((sheafificationAdjunction (affineIndEtaleTopology Z)
                  AddCommGrpCat.{u + 1}).unit.app
                ((AffineIndEtale.lift i).op ⋙ G.obj)).app
                  (op V.obj)))).toEquiv.trans <|
          ((uliftYonedaEquiv.{u + 1} :
                (uliftYoneda.{u + 1}.obj V.obj ⟶
                  ((abelianInverseImage i).obj G).obj ⋙
                    CategoryTheory.forget AddCommGrpCat.{u + 1}) ≃
                (((abelianInverseImage i).obj G).obj ⋙
                    CategoryTheory.forget AddCommGrpCat.{u + 1}).obj
                  (op V.obj))).symm.trans <|
            (FreeAbelianPresheaf.homEquiv (uliftYoneda.{u + 1}.obj V.obj)
                  ((abelianInverseImage i).obj G).obj).symm.trans
              ((sheafificationAdjunction (affineIndEtaleTopology Z)
                    AddCommGrpCat.{u + 1}).homEquiv
                  (FreeAbelianPresheaf.obj (uliftYoneda.{u + 1}.obj V.obj))
                  ((abelianInverseImage i).obj G)).symm

/-- The generator unit is the transpose of the identity under the actual
weakly contractible evaluation equivalence. -/
def AffineIndEtale.abelianLiftGeneratorUnit
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    (V : (weaklyContractible Z).FullSubcategory) :
    weaklyContractibleFreeAbelianObj Z V ⟶
      (abelianInverseImage i).obj
        ((affineIndEtaleTopology X).freeAbelianSheafFunctor.obj
          (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj))) :=
  abelianLowerShriekRepresentableHomEquiv i V _ (𝟙 _)

/-- Lift free generators using their evaluation Hom equivalence on every
abelian sheaf morphism, including addition, negation, and zero maps. -/
def AffineIndEtale.weaklyContractibleLiftFreeAbelian
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}] :
    WeaklyContractibleAbelian Z ⥤
      Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1} where
  obj V := (affineIndEtaleTopology X).freeAbelianSheafFunctor.obj
    (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj))
  map {V W} f := (abelianLowerShriekRepresentableHomEquiv i V _).symm
    (f.hom ≫ abelianLiftGeneratorUnit i W)
  map_id := sorry
  map_comp := sorry

/-- On objects the lift retains precisely the source-specified free abelian sheaf. -/
theorem AffineIndEtale.weaklyContractibleLiftFreeAbelian_obj
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    (V : WeaklyContractibleAbelian Z) :
    (weaklyContractibleLiftFreeAbelian i).obj V =
      (affineIndEtaleTopology X).freeAbelianSheafFunctor.obj
        (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj)) := rfl

/-- The map is characterized by the actual generator unit and transpose,
not by an arbitrary comparison isomorphism. -/
theorem AffineIndEtale.weaklyContractibleLiftFreeAbelian_map_spec
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    {V W : WeaklyContractibleAbelian Z} (f : V ⟶ W) :
    abelianLowerShriekRepresentableHomEquiv i V _
        ((weaklyContractibleLiftFreeAbelian i).map f) =
      f.hom ≫ abelianLiftGeneratorUnit i W :=
  (abelianLowerShriekRepresentableHomEquiv i V _).apply_symm_apply _

/-- Transposing arbitrary additive maps gives the actual naturality square
with the generator units and the specified abelian inverse image. -/
theorem AffineIndEtale.abelianLiftGeneratorUnit_naturality
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    {V W : WeaklyContractibleAbelian Z} (f : V ⟶ W) :
    abelianLiftGeneratorUnit i V ≫
        (abelianInverseImage i).map ((weaklyContractibleLiftFreeAbelian i).map f) =
      f.hom ≫ abelianLiftGeneratorUnit i W := sorry

/-- On morphisms coming from affine schemes, the additive extension agrees
with the original free-abelian map of the geometric lift v. -/
theorem AffineIndEtale.weaklyContractibleLiftFreeAbelian_map_scheme
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    {V W : (weaklyContractible Z).FullSubcategory} (f : V ⟶ W) :
    (weaklyContractibleLiftFreeAbelian i).map
        (InducedCategory.homMk
          ((affineIndEtaleTopology Z).freeAbelianSheafFunctor.map
            (uliftYoneda.{u + 1}.map f.hom))) =
      (affineIndEtaleTopology X).freeAbelianSheafFunctor.map
        (uliftYoneda.{u + 1}.map ((AffineIndEtale.lift i).map f.hom)) := sorry

/-- Abelian lower shriek along the affine ind-étale lift of a closed immersion
of affine schemes, as sheaf-category left Kan extension of `ℤ_V ↦ ℤ_{v(V)}` on
weakly contractible objects. -/
def AffineIndEtale.abelianLowerShriek (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)] :
    Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1} ⥤
      Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (weaklyContractibleFreeAbelian Z).leftKanExtension
    (weaklyContractibleLiftFreeAbelian i)

/-- Abelian lower shriek is sheaf-category left Kan extension of
`V ↦ ℤ_{v(V)}` along weakly contractible free abelian representables. -/
theorem AffineIndEtale.abelianLowerShriek_def (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)] :
    abelianLowerShriek i =
      (weaklyContractibleFreeAbelian Z).leftKanExtension
        (weaklyContractibleLiftFreeAbelian i) :=
  sorry

/-- The Kan-extension unit component `ℤ_{v(V)} ⟶ i_! ℤ_V` is an isomorphism on
weakly contractible objects. -/
instance AffineIndEtale.abelianLowerShriek_leftKanExtensionUnit_app_isIso
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)]
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    IsIso
      (((weaklyContractibleFreeAbelian Z).leftKanExtensionUnit
          (weaklyContractibleLiftFreeAbelian i)).app
        ⟨V, ‹(affineIndEtaleTopology Z).IsWeaklyContractible V›⟩) :=
  sorry

/-- On a weakly contractible object, abelian lower shriek sends `ℤ_V` to
`ℤ_{v(V)}`. -/
def AffineIndEtale.abelianLowerShriek_obj_freeAbelian
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)]
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    (abelianLowerShriek i).obj
        ((affineIndEtaleTopology Z).freeAbelianSheafFunctor.obj
          (uliftYoneda.{u + 1}.obj V)) ≅
      (affineIndEtaleTopology X).freeAbelianSheafFunctor.obj
        (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V)) :=
  (asIso
      (((weaklyContractibleFreeAbelian Z).leftKanExtensionUnit
          (weaklyContractibleLiftFreeAbelian i)).app
        ⟨V, ‹(affineIndEtaleTopology Z).IsWeaklyContractible V›⟩)).symm

/-- Cocones of maps `ℤ_{v(V)} ⟶ G` are equivalent to cocones of maps
`ℤ_V ⟶ i⁻¹ G`. -/
def AffineIndEtale.abelianLowerShriekCoconeEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    (F : Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1})
    (G : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}) :
    { p :
          ∀ α : CostructuredArrow (weaklyContractibleFreeAbelian Z) F,
            (weaklyContractibleLiftFreeAbelian i).obj α.left ⟶ G //
        ∀ {α β : CostructuredArrow (weaklyContractibleFreeAbelian Z) F}
          (f : α ⟶ β),
          (weaklyContractibleLiftFreeAbelian i).map f.left ≫ p β = p α } ≃
      { p :
          ∀ α : CostructuredArrow (weaklyContractibleFreeAbelian Z) F,
            (weaklyContractibleFreeAbelian Z).obj α.left ⟶
              (abelianInverseImage i).obj G //
        ∀ {α β : CostructuredArrow (weaklyContractibleFreeAbelian Z) F}
          (f : α ⟶ β),
          (weaklyContractibleFreeAbelian Z).map f.left ≫ p β = p α } where
  toFun p :=
    ⟨fun α => abelianLowerShriekRepresentableHomEquiv i α.left G (p.1 α),
      sorry⟩
  invFun q :=
    ⟨fun α =>
      (abelianLowerShriekRepresentableHomEquiv i α.left G).symm (q.1 α),
      sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- Morphisms out of the colimit of `ℤ_{v(V)}` over an abelian sheaf identify
with cocones of those maps. -/
def AffineIndEtale.abelianLowerShriekColimitHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)]
    (F : Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1})
    (G : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (colimit
          (CostructuredArrow.proj (weaklyContractibleFreeAbelian Z) F ⋙
            weaklyContractibleLiftFreeAbelian i) ⟶
        G) ≃
      { p :
          ∀ α : CostructuredArrow (weaklyContractibleFreeAbelian Z) F,
            (weaklyContractibleLiftFreeAbelian i).obj α.left ⟶ G //
        ∀ {α β : CostructuredArrow (weaklyContractibleFreeAbelian Z) F}
          (f : α ⟶ β),
          (weaklyContractibleLiftFreeAbelian i).map f.left ≫ p β = p α } :=
  Equiv.ulift.symm.trans
    (colimit.homIso'
        (CostructuredArrow.proj (weaklyContractibleFreeAbelian Z) F ⋙
          weaklyContractibleLiftFreeAbelian i)
        G).toEquiv

/-- Morphisms out of the colimit of `ℤ_V` over an abelian sheaf identify with
cocones of those maps. -/
def AffineIndEtale.abelianLowerShriekSourceColimitHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    (F : Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1})
    (G : Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    (colimit
          (CostructuredArrow.proj (weaklyContractibleFreeAbelian Z) F ⋙
            weaklyContractibleFreeAbelian Z) ⟶
        G) ≃
      { p :
          ∀ α : CostructuredArrow (weaklyContractibleFreeAbelian Z) F,
            (weaklyContractibleFreeAbelian Z).obj α.left ⟶ G //
        ∀ {α β : CostructuredArrow (weaklyContractibleFreeAbelian Z) F}
          (f : α ⟶ β),
          (weaklyContractibleFreeAbelian Z).map f.left ≫ p β = p α } :=
  Equiv.ulift.symm.trans
    (colimit.homIso'
        (CostructuredArrow.proj (weaklyContractibleFreeAbelian Z) F ⋙
          weaklyContractibleFreeAbelian Z)
        G).toEquiv

/-- Hom-equivalence exhibiting abelian lower shriek as left adjoint of abelian
inverse image along `v`. -/
def AffineIndEtale.abelianLowerShriekHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)]
    (F : Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1})
    (G : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}) :
    ((abelianLowerShriek i).obj F ⟶ G) ≃
      (F ⟶ (abelianInverseImage i).obj G) :=
  (((weaklyContractibleFreeAbelian Z).leftKanExtensionObjIsoColimit
            (weaklyContractibleLiftFreeAbelian i) F).homCongr
        (Iso.refl G)).trans <|
    (abelianLowerShriekColimitHomEquiv i F G).trans <|
      (abelianLowerShriekCoconeEquiv i F G).trans <|
        (abelianLowerShriekSourceColimitHomEquiv i F
              ((abelianInverseImage i).obj G)).symm.trans <|
          (((weaklyContractibleFreeAbelian Z).leftKanExtensionObjIsoColimit
                    (weaklyContractibleFreeAbelian Z) F).symm.homCongr
                (Iso.refl ((abelianInverseImage i).obj G))).trans
            (((IsDense.leftKanExtensionIso
                      (weaklyContractibleFreeAbelian Z)).app
                    F).homCongr
                (Iso.refl ((abelianInverseImage i).obj G)))

/-- The packaged adjunction `i_! ⊣ i⁻¹` on abelian sheaves, whose unit is
`id ⟶ i⁻¹ i_!`. -/
def AffineIndEtale.abelianLowerShriekAdjunction (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)] :
    abelianLowerShriek i ⊣ abelianInverseImage i :=
  Adjunction.mkOfHomEquiv
    { homEquiv := abelianLowerShriekHomEquiv i
      homEquiv_naturality_left_symm := fun _ _ => sorry
      homEquiv_naturality_right := fun _ _ => sorry }

/-- The unit of abelian lower shriek is the unit of
`abelianLowerShriekAdjunction`. -/
theorem AffineIndEtale.abelianLowerShriekAdjunction_unit (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)]
    (F : Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    (abelianLowerShriekAdjunction i).unit.app F =
      (abelianLowerShriekHomEquiv i F ((abelianLowerShriek i).obj F))
        (𝟙 _) :=
  sorry

/-- The unit `id ⟶ i⁻¹ i_!` is an isomorphism. -/
instance AffineIndEtale.abelianLowerShriek_unit_isIso (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)] :
    IsIso (abelianLowerShriekAdjunction i).unit := sorry

/-- Abelian lower shriek is fully faithful, as its adjunction unit is an
isomorphism. -/
def AffineIndEtale.abelianLowerShriekFullyFaithful (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)] :
    (abelianLowerShriek i).FullyFaithful :=
  (abelianLowerShriekAdjunction i).fullyFaithfulLOfIsIsoUnit

/-- The counit `i⁻¹ i_* ⟶ id` of the type-valued morphism of topoi associated
to `v` is an isomorphism. -/
instance AffineIndEtale.inverseImage_pushforward_counit_isIso (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    IsIso (morphismOfTopoi i).adjunction.counit := sorry

/-- Type-valued direct image along `v` is a full functor. -/
instance AffineIndEtale.lift_sheafPushforwardCocontinuous_full
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    ((AffineIndEtale.lift i).sheafPushforwardCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).Full := sorry

/-- Type-valued direct image along `v` is a faithful functor. -/
instance AffineIndEtale.lift_sheafPushforwardCocontinuous_faithful
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    ((AffineIndEtale.lift i).sheafPushforwardCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).Faithful :=
  sorry

/-- Type-valued direct image along `v` is fully faithful. -/
def AffineIndEtale.lift_sheafPushforwardCocontinuousFullyFaithful
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    ((AffineIndEtale.lift i).sheafPushforwardCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful
    ((AffineIndEtale.lift i).sheafPushforwardCocontinuous (Type (u + 1))
      (affineIndEtaleTopology Z) (affineIndEtaleTopology X))

/-- Abelian direct image along `v` is a full functor. -/
instance AffineIndEtale.lift_abelianSheafPushforwardCocontinuous_full
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    ((AffineIndEtale.lift i).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).Full := sorry

/-- Abelian direct image along `v` is a faithful functor. -/
instance AffineIndEtale.lift_abelianSheafPushforwardCocontinuous_faithful
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    ((AffineIndEtale.lift i).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).Faithful :=
  sorry

/-- Abelian direct image along `v` is fully faithful. -/
def AffineIndEtale.lift_abelianSheafPushforwardCocontinuousFullyFaithful
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    ((AffineIndEtale.lift i).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful
    ((AffineIndEtale.lift i).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (affineIndEtaleTopology Z) (affineIndEtaleTopology X))

/-- Small type-valued lower shriek, conjugated along affine ind-étale
restriction. -/
def AffineIndEtale.smallSheafLowerShriek (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)]
    [∀ F : (AffineIndEtale X)ᵒᵖ ⥤ Type (u + 1),
      (affineIndEtaleInclusion X).op.HasPointwiseRightKanExtension F] :
    Sheaf (topology Z) (Type (u + 1)) ⥤ Sheaf (topology X) (Type (u + 1)) :=
  affineIndEtaleRestriction Z ⋙ sheafLowerShriek i ⋙
    (affineIndEtaleInclusion X).sheafPushforwardCocontinuous (Type (u + 1))
      (affineIndEtaleTopology X) (topology X)

/-- Small type-valued lower shriek is restriction, app-site lower shriek, and
cocontinuous extension. -/
theorem AffineIndEtale.smallSheafLowerShriek_def (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasPointwiseLeftKanExtension
      (weaklyContractibleSheafifiedRepresentable Z)
      (weaklyContractibleLiftSheafifiedRepresentable i)]
    [∀ F : (AffineIndEtale X)ᵒᵖ ⥤ Type (u + 1),
      (affineIndEtaleInclusion X).op.HasPointwiseRightKanExtension F] :
    smallSheafLowerShriek i =
      affineIndEtaleRestriction Z ⋙ sheafLowerShriek i ⋙
        (affineIndEtaleInclusion X).sheafPushforwardCocontinuous (Type (u + 1))
          (affineIndEtaleTopology X) (topology X) :=
  sorry

/-- Small abelian lower shriek, conjugated along affine ind-étale restriction. -/
def AffineIndEtale.smallAbelianLowerShriek (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)]
    [∀ F : (AffineIndEtale X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (affineIndEtaleInclusion X).op.HasPointwiseRightKanExtension F] :
    Sheaf (topology Z) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology X) AddCommGrpCat.{u + 1} :=
  (affineIndEtaleInclusion Z).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (affineIndEtaleTopology Z) (topology Z) ⋙
    abelianLowerShriek i ⋙
    (affineIndEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (affineIndEtaleTopology X) (topology X)

/-- Small abelian lower shriek is restriction, app-site lower shriek, and
cocontinuous extension. -/
theorem AffineIndEtale.smallAbelianLowerShriek_def (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    [HasPointwiseLeftKanExtension (weaklyContractibleFreeAbelian Z)
      (weaklyContractibleLiftFreeAbelian i)]
    [∀ F : (AffineIndEtale X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (affineIndEtaleInclusion X).op.HasPointwiseRightKanExtension F] :
    smallAbelianLowerShriek i =
      (affineIndEtaleInclusion Z).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (affineIndEtaleTopology Z) (topology Z) ⋙
        abelianLowerShriek i ⋙
        (affineIndEtaleInclusion X).sheafPushforwardCocontinuous
          AddCommGrpCat.{u + 1} (affineIndEtaleTopology X) (topology X) :=
  sorry

end AlgebraicGeometry.Scheme.ProEt
