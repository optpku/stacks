module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Functor.FreeAbelian
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelian
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Hom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtaleTopos

/-!
# Lower shriek along an affine closed immersion

Left adjoints of inverse image on affine ind-étale sites are obtained by
sending weakly contractible representables `h_V` to `h_{v(V)}` (and `ℤ_V` to
`ℤ_{v(V)}`) and extending by colimits along that full subcategory of the
sheaf category. This is not presheaf left Kan extension along `v`.
-/

public section

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

namespace AffineIndEtale

/-- Weakly contractible objects of the affine ind-étale site, as an object
property. -/
@[expose] def weaklyContractible (S : Scheme.{u}) [IsAffine S] :
    ObjectProperty (AffineIndEtale S) :=
  fun U ↦ (affineIndEtaleTopology S).IsWeaklyContractible U

/-- Weakly contractible objects are those for which the affine ind-étale
topology is weakly contractible. -/
theorem weaklyContractible_iff (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    weaklyContractible S U ↔
      (affineIndEtaleTopology S).IsWeaklyContractible U :=
  Iff.rfl

/-- Objects of the weakly contractible full subcategory are weakly
contractible. -/
instance weaklyContractible_obj
    (S : Scheme.{u}) [IsAffine S]
    (V : (weaklyContractible S).FullSubcategory) :
    (affineIndEtaleTopology S).IsWeaklyContractible V.obj :=
  V.property


/-- Sheafified Yoneda on weakly contractible affine ind-étale objects. -/
@[expose] def weaklyContractibleSheafifiedRepresentable
    (S : Scheme.{u}) [IsAffine S] :
    (weaklyContractible S).FullSubcategory ⥤
      Sheaf (affineIndEtaleTopology S) (Type (u + 1)) :=
  (weaklyContractible S).ι ⋙
    (affineIndEtaleTopology S).sheafifiedRepresentableFunctor

/-- Sheafified Yoneda on weakly contractible objects is inclusion followed by
sheafified representables. -/
theorem weaklyContractibleSheafifiedRepresentable_def
    (S : Scheme.{u}) [IsAffine S] :
    weaklyContractibleSheafifiedRepresentable S =
      (weaklyContractible S).ι ⋙
        (affineIndEtaleTopology S).sheafifiedRepresentableFunctor :=
  rfl

/-- Weakly contractible sheafified representables generate the category of
type-valued sheaves on the affine ind-étale site. -/
instance weaklyContractibleSheafifiedRepresentable_isDense
    (S : Scheme.{u}) [IsAffine S] :
    (weaklyContractibleSheafifiedRepresentable S).IsDense := sorry

/-- Sheafified Yoneda of the image of a weakly contractible object under the
affine ind-étale lift `v`. -/
@[expose] def weaklyContractibleLiftSheafifiedRepresentable
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (weaklyContractible Z).FullSubcategory ⥤
      Sheaf (affineIndEtaleTopology X) (Type (u + 1)) :=
  (weaklyContractible Z).ι ⋙
    AffineIndEtale.lift i ⋙
    (affineIndEtaleTopology X).sheafifiedRepresentableFunctor

/-- The lift of weakly contractible sheafified representables is inclusion,
then `v`, then sheafified Yoneda. -/
theorem weaklyContractibleLiftSheafifiedRepresentable_def
    (i : Z ⟶ X) [IsClosedImmersion i] :
    weaklyContractibleLiftSheafifiedRepresentable i =
      (weaklyContractible Z).ι ⋙
        AffineIndEtale.lift i ⋙
        (affineIndEtaleTopology X).sheafifiedRepresentableFunctor :=
  rfl

/-- Type-valued lower shriek along the affine ind-étale lift of a closed
immersion of affine schemes, as sheaf-category left Kan extension of
`h_V ↦ h_{v(V)}` on weakly contractible objects. -/
@[expose] def sheafLowerShriek (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf (affineIndEtaleTopology Z) (Type (u + 1)) ⥤
      Sheaf (affineIndEtaleTopology X) (Type (u + 1)) :=
  (weaklyContractibleSheafifiedRepresentable Z).leftKanExtension
    (weaklyContractibleLiftSheafifiedRepresentable i)

/-- Type-valued lower shriek is sheaf-category left Kan extension of
`V ↦ h_{v(V)}` along weakly contractible sheafified representables. -/
theorem sheafLowerShriek_def (i : Z ⟶ X) [IsClosedImmersion i] :
    sheafLowerShriek i =
      (weaklyContractibleSheafifiedRepresentable Z).leftKanExtension
        (weaklyContractibleLiftSheafifiedRepresentable i) :=
  rfl

/-- The Kan-extension unit component `h_{v(V)} ⟶ i^{Sh}_! h_V` is an
isomorphism on weakly contractible objects. -/
instance sheafLowerShriek_leftKanExtensionUnit_app_isIso
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    IsIso
      (((weaklyContractibleSheafifiedRepresentable Z).leftKanExtensionUnit
          (weaklyContractibleLiftSheafifiedRepresentable i)).app
        ⟨V, ‹(affineIndEtaleTopology Z).IsWeaklyContractible V›⟩) :=
  sorry

/-- On a weakly contractible object, type-valued lower shriek sends the
sheafified representable `h_V` to `h_{v(V)}`. -/
@[expose] def sheafLowerShriek_obj_sheafifiedRepresentable
    (i : Z ⟶ X) [IsClosedImmersion i]
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
theorem sheafLowerShriek_obj_sheafifiedRepresentable_inv
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    (sheafLowerShriek_obj_sheafifiedRepresentable i V).inv =
      ((weaklyContractibleSheafifiedRepresentable Z).leftKanExtensionUnit
          (weaklyContractibleLiftSheafifiedRepresentable i)).app
        ⟨V, ‹(affineIndEtaleTopology Z).IsWeaklyContractible V›⟩ :=
  rfl

/-- Hom-equivalence `Hom(h_{v(V)}, G) ≃ Hom(h_V, i⁻¹ G)` on a weakly
contractible object. -/
@[expose] def sheafLowerShriekRepresentableHomEquiv
    (i : Z ⟶ X) [IsClosedImmersion i]
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
    (asIso (inverseImage_obj_to i G V.obj)).toEquiv.trans
      (((affineIndEtaleTopology Z).sheafifiedRepresentableHomEquiv
          (((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
              (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).obj G)
          V.obj).symm)

/-- Transposition of sheafified representable generators preserves compatible cocones. -/
private theorem sheafLowerShriekCoconeEquiv_toFun_naturality (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology Z) (Type (u + 1)))
    (G : Sheaf (affineIndEtaleTopology X) (Type (u + 1)))
    (p : { p :
          ∀ α : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F,
            (weaklyContractibleLiftSheafifiedRepresentable i).obj α.left ⟶ G //
        ∀ {α β : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F}
          (f : α ⟶ β),
          (weaklyContractibleLiftSheafifiedRepresentable i).map f.left ≫
              p β =
            p α }) :
    ∀ {α β : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F}
          (f : α ⟶ β),
          (weaklyContractibleSheafifiedRepresentable Z).map f.left ≫ (sheafLowerShriekRepresentableHomEquiv i β.left G (p.1 β)) =
            (sheafLowerShriekRepresentableHomEquiv i α.left G (p.1 α)) := sorry

private theorem sheafLowerShriekCoconeEquiv_invFun_naturality (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology Z) (Type (u + 1)))
    (G : Sheaf (affineIndEtaleTopology X) (Type (u + 1)))
    (p : { p :
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
            p α }) :
    ∀ {α β : CostructuredArrow
              (weaklyContractibleSheafifiedRepresentable Z) F}
          (f : α ⟶ β),
          (weaklyContractibleLiftSheafifiedRepresentable i).map f.left ≫
              ((sheafLowerShriekRepresentableHomEquiv i β.left G).symm (p.1 β)) =
            ((sheafLowerShriekRepresentableHomEquiv i α.left G).symm (p.1 α)) := sorry

private def sheafLowerShriekCoconeEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
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
    ⟨fun α => sheafLowerShriekRepresentableHomEquiv i α.left G (p.1 α), sheafLowerShriekCoconeEquiv_toFun_naturality i F G p⟩
  invFun q :=
    ⟨fun α => (sheafLowerShriekRepresentableHomEquiv i α.left G).symm (q.1 α),
      sheafLowerShriekCoconeEquiv_invFun_naturality i F G q⟩
  left_inv p := by
    apply Subtype.ext
    funext α
    exact (sheafLowerShriekRepresentableHomEquiv i α.left G).symm_apply_apply (p.1 α)
  right_inv p := by
    apply Subtype.ext
    funext α
    exact (sheafLowerShriekRepresentableHomEquiv i α.left G).apply_symm_apply (p.1 α)

/-- Morphisms out of the colimit of `h_{v(V)}` over a sheaf identify with
cocones of those maps. -/
private def sheafLowerShriekColimitHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
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
private def sheafLowerShriekSourceColimitHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
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
def sheafLowerShriekHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
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

/-- The lower-shriek Hom equivalence commutes with precomposition in the source sheaf. -/
private theorem sheafLowerShriekHomEquiv_naturality_left_symm
    (i : Z ⟶ X) [IsClosedImmersion i]
    {F' F : Sheaf (affineIndEtaleTopology Z) (Type (u + 1))}
    {G : Sheaf (affineIndEtaleTopology X) (Type (u + 1))}
    (f : F' ⟶ F) (g : F ⟶ ((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).obj G) :
    (sheafLowerShriekHomEquiv i F' G).symm (f ≫ g) =
      (sheafLowerShriek i).map f ≫ (sheafLowerShriekHomEquiv i F G).symm g := sorry

private theorem sheafLowerShriekHomEquiv_naturality_right
    (i : Z ⟶ X) [IsClosedImmersion i]
    {F : Sheaf (affineIndEtaleTopology Z) (Type (u + 1))}
    {G G' : Sheaf (affineIndEtaleTopology X) (Type (u + 1))}
    (f : (sheafLowerShriek i).obj F ⟶ G) (g : G ⟶ G') :
    sheafLowerShriekHomEquiv i F G' (f ≫ g) =
      sheafLowerShriekHomEquiv i F G f ≫ ((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).map g := sorry

/-- Lower shriek is left adjoint to inverse image on type-valued sheaves. -/
@[expose] def sheafLowerShriekAdjunction (i : Z ⟶ X)
    [IsClosedImmersion i] :
    sheafLowerShriek i ⊣
      (AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sheafLowerShriekHomEquiv i
      homEquiv_naturality_left_symm := by exact sheafLowerShriekHomEquiv_naturality_left_symm i
      homEquiv_naturality_right := by exact sheafLowerShriekHomEquiv_naturality_right i }

/-- The unit of type-valued lower shriek is the unit of
`sheafLowerShriekAdjunction`. -/
theorem sheafLowerShriekAdjunction_unit (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology Z) (Type (u + 1))) :
    (sheafLowerShriekAdjunction i).unit.app F =
      (sheafLowerShriekHomEquiv i F
          ((sheafLowerShriek i).obj F)) (𝟙 _) :=
  rfl

/-- The unit `id ⟶ i⁻¹ i^{Sh}_!` is an isomorphism. -/
instance sheafLowerShriek_unit_isIso (i : Z ⟶ X)
    [IsClosedImmersion i] :
    IsIso (sheafLowerShriekAdjunction i).unit := sorry

/-- Type-valued lower shriek is fully faithful, as its adjunction unit is an
isomorphism. -/
@[expose] def sheafLowerShriekFullyFaithful (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (sheafLowerShriek i).FullyFaithful :=
  (sheafLowerShriekAdjunction i).fullyFaithfulLOfIsIsoUnit

/-- Free abelian sheaf represented by a weakly contractible affine object. -/
abbrev weaklyContractibleFreeAbelianObj
    (S : Scheme.{u}) [IsAffine S]
    (V : (weaklyContractible S).FullSubcategory) :
    Sheaf (affineIndEtaleTopology S) AddCommGrpCat.{u + 1} :=
  (affineIndEtaleTopology S).freeAbelianSheafFunctor.{u + 1}.obj
    (uliftYoneda.{u + 1}.obj V.obj)

/-- Weakly contractible free abelian generators with ALL abelian sheaf morphisms.
The induced category retains additive relations, not just scheme reindexing maps. -/
abbrev WeaklyContractibleAbelian
    (S : Scheme.{u}) [IsAffine S] :=
  InducedCategory (Sheaf (affineIndEtaleTopology S) AddCommGrpCat.{u + 1})
    (weaklyContractibleFreeAbelianObj S)

/-- The fully faithful inclusion of these free generators into abelian sheaves. -/
@[expose] def weaklyContractibleFreeAbelian
    (S : Scheme.{u}) [IsAffine S] :
    WeaklyContractibleAbelian S ⥤
      Sheaf (affineIndEtaleTopology S) AddCommGrpCat.{u + 1} :=
  inducedFunctor (weaklyContractibleFreeAbelianObj S)

/-- The inclusion uses the canonical induced-category functor. -/
theorem weaklyContractibleFreeAbelian_def
    (S : Scheme.{u}) [IsAffine S] :
    weaklyContractibleFreeAbelian S =
      inducedFunctor (weaklyContractibleFreeAbelianObj S) := rfl

/-- A morphism in the generator category is its specified abelian sheaf map. -/
theorem weaklyContractibleFreeAbelian_map
    (S : Scheme.{u}) [IsAffine S]
    {V W : WeaklyContractibleAbelian S} (f : V ⟶ W) :
    (weaklyContractibleFreeAbelian S).map f = f.hom := rfl

/-- The full free-generator subcategory is dense: weakly contractible covers
generate, and finite disjoint unions provide finite sums with all linear maps. -/
instance weaklyContractibleFreeAbelian_isDense
    (S : Scheme.{u}) [IsAffine S] :
    (weaklyContractibleFreeAbelian S).IsDense := sorry

/-- On a weakly contractible object, the sheafification unit of abelian
inverse image is an isomorphism. -/
instance abelianInverseImage_sheafifyUnit_app_isIso
    (i : Z ⟶ X) [IsClosedImmersion i]
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
@[expose] def abelianLowerShriekRepresentableHomEquiv
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : (weaklyContractible Z).FullSubcategory)
    (G : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}) :
    ((affineIndEtaleTopology X).freeAbelianSheafFunctor.{u + 1}.obj
          (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj)) ⟶
        G) ≃
      ((affineIndEtaleTopology Z).freeAbelianSheafFunctor.{u + 1}.obj
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
@[expose] def abelianLiftGeneratorUnit
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : (weaklyContractible Z).FullSubcategory) :
    weaklyContractibleFreeAbelianObj Z V ⟶
      (abelianInverseImage i).obj
        ((affineIndEtaleTopology X).freeAbelianSheafFunctor.{u + 1}.obj
          (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj))) :=
  abelianLowerShriekRepresentableHomEquiv i V _ (𝟙 _)

private def weaklyContractibleLiftFreeAbelianMap
    (i : Z ⟶ X) [IsClosedImmersion i]
    {V W : WeaklyContractibleAbelian Z} (f : V ⟶ W) :
    (affineIndEtaleTopology X).freeAbelianSheafFunctor.{u + 1}.obj
        (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj)) ⟶
      (affineIndEtaleTopology X).freeAbelianSheafFunctor.{u + 1}.obj
        (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj W.obj)) :=
  (abelianLowerShriekRepresentableHomEquiv i V _).symm
    (f.hom ≫ abelianLiftGeneratorUnit i W)

/-- Transposing arbitrary additive maps gives the actual naturality square
with the generator units and the specified abelian inverse image. -/
private theorem abelianLiftGeneratorUnit_naturality
    (i : Z ⟶ X) [IsClosedImmersion i]
    {V W : WeaklyContractibleAbelian Z} (f : V ⟶ W) :
    abelianLiftGeneratorUnit i V ≫
        (abelianInverseImage i).map (weaklyContractibleLiftFreeAbelianMap i f) =
      f.hom ≫ abelianLiftGeneratorUnit i W := sorry

private theorem weaklyContractibleLiftFreeAbelianMap_id
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : WeaklyContractibleAbelian Z) :
    weaklyContractibleLiftFreeAbelianMap i (𝟙 V) = 𝟙 _ := sorry

private theorem weaklyContractibleLiftFreeAbelianMap_comp
    (i : Z ⟶ X) [IsClosedImmersion i]
    {U V W : WeaklyContractibleAbelian Z} (f : U ⟶ V) (g : V ⟶ W) :
    weaklyContractibleLiftFreeAbelianMap i (f ≫ g) =
      weaklyContractibleLiftFreeAbelianMap i f ≫
        weaklyContractibleLiftFreeAbelianMap i g := sorry

/-- The affine lift extends to all additive morphisms between weakly
contractible free abelian generators. -/
@[expose] def weaklyContractibleLiftFreeAbelian
    (i : Z ⟶ X) [IsClosedImmersion i] :
    WeaklyContractibleAbelian Z ⥤
      Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1} where
  obj V := (affineIndEtaleTopology X).freeAbelianSheafFunctor.{u + 1}.obj
    (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj))
  map {V W} f := (abelianLowerShriekRepresentableHomEquiv i V _).symm
    (f.hom ≫ abelianLiftGeneratorUnit i W)
  map_id := by exact weaklyContractibleLiftFreeAbelianMap_id i
  map_comp := by exact weaklyContractibleLiftFreeAbelianMap_comp i

/-- The lifted generator at `V` is the free abelian sheaf represented by `lift i V`. -/
theorem weaklyContractibleLiftFreeAbelian_obj
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : WeaklyContractibleAbelian Z) :
    (weaklyContractibleLiftFreeAbelian i).obj V =
      (affineIndEtaleTopology X).freeAbelianSheafFunctor.{u + 1}.obj
        (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V.obj)) := rfl

/-- The map is characterized by the actual generator unit and transpose,
not by an arbitrary comparison isomorphism. -/
theorem weaklyContractibleLiftFreeAbelian_map_spec
    (i : Z ⟶ X) [IsClosedImmersion i]
    {V W : WeaklyContractibleAbelian Z} (f : V ⟶ W) :
    abelianLowerShriekRepresentableHomEquiv i V _
        ((weaklyContractibleLiftFreeAbelian i).map f) =
      f.hom ≫ abelianLiftGeneratorUnit i W :=
  (abelianLowerShriekRepresentableHomEquiv i V _).apply_symm_apply _

/-- On morphisms coming from affine schemes, the additive extension agrees
with the original free-abelian map of the geometric lift v. -/
theorem weaklyContractibleLiftFreeAbelian_map_scheme
    (i : Z ⟶ X) [IsClosedImmersion i]
    {V W : (weaklyContractible Z).FullSubcategory} (f : V ⟶ W) :
    (weaklyContractibleLiftFreeAbelian i).map
        (InducedCategory.homMk
          ((affineIndEtaleTopology Z).freeAbelianSheafFunctor.{u + 1}.map
            (uliftYoneda.{u + 1}.map f.hom))) =
      (affineIndEtaleTopology X).freeAbelianSheafFunctor.{u + 1}.map
        (uliftYoneda.{u + 1}.map ((AffineIndEtale.lift i).map f.hom)) := sorry

/-- Abelian lower shriek along the affine ind-étale lift of a closed immersion
of affine schemes, as sheaf-category left Kan extension of `ℤ_V ↦ ℤ_{v(V)}` on
weakly contractible objects. -/
@[expose] def abelianLowerShriek (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1} ⥤
      Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (weaklyContractibleFreeAbelian Z).leftKanExtension
    (weaklyContractibleLiftFreeAbelian i)

/-- Abelian lower shriek is sheaf-category left Kan extension of
`V ↦ ℤ_{v(V)}` along weakly contractible free abelian representables. -/
theorem abelianLowerShriek_def (i : Z ⟶ X)
    [IsClosedImmersion i] :
    abelianLowerShriek i =
      (weaklyContractibleFreeAbelian Z).leftKanExtension
        (weaklyContractibleLiftFreeAbelian i) :=
  rfl

/-- The Kan-extension unit component `ℤ_{v(V)} ⟶ i_! ℤ_V` is an isomorphism on
weakly contractible objects. -/
instance abelianLowerShriek_leftKanExtensionUnit_app_isIso
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    IsIso
      (((weaklyContractibleFreeAbelian Z).leftKanExtensionUnit
          (weaklyContractibleLiftFreeAbelian i)).app
        ⟨V, ‹(affineIndEtaleTopology Z).IsWeaklyContractible V›⟩) :=
  sorry

/-- On a weakly contractible object, abelian lower shriek sends `ℤ_V` to
`ℤ_{v(V)}`. -/
@[expose] def abelianLowerShriek_obj_freeAbelian
    (i : Z ⟶ X) [IsClosedImmersion i]
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    (abelianLowerShriek i).obj
        ((affineIndEtaleTopology Z).freeAbelianSheafFunctor.{u + 1}.obj
          (uliftYoneda.{u + 1}.obj V)) ≅
      (affineIndEtaleTopology X).freeAbelianSheafFunctor.{u + 1}.obj
        (uliftYoneda.{u + 1}.obj ((AffineIndEtale.lift i).obj V)) :=
  (asIso
      (((weaklyContractibleFreeAbelian Z).leftKanExtensionUnit
          (weaklyContractibleLiftFreeAbelian i)).app
        ⟨V, ‹(affineIndEtaleTopology Z).IsWeaklyContractible V›⟩)).symm

/-- Transposition of free abelian generators preserves compatible cocones. -/
private theorem abelianLowerShriekCoconeEquiv_toFun_naturality (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1})
    (G : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1})
    (p : { p :
          ∀ α : CostructuredArrow (weaklyContractibleFreeAbelian Z) F,
            (weaklyContractibleLiftFreeAbelian i).obj α.left ⟶ G //
        ∀ {α β : CostructuredArrow (weaklyContractibleFreeAbelian Z) F}
          (f : α ⟶ β),
          (weaklyContractibleLiftFreeAbelian i).map f.left ≫ p β = p α }) :
    ∀ {α β : CostructuredArrow (weaklyContractibleFreeAbelian Z) F}
          (f : α ⟶ β),
          (weaklyContractibleFreeAbelian Z).map f.left ≫ (abelianLowerShriekRepresentableHomEquiv i β.left G (p.1 β)) = (abelianLowerShriekRepresentableHomEquiv i α.left G (p.1 α)) := sorry

private theorem abelianLowerShriekCoconeEquiv_invFun_naturality (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1})
    (G : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1})
    (p : { p :
          ∀ α : CostructuredArrow (weaklyContractibleFreeAbelian Z) F,
            (weaklyContractibleFreeAbelian Z).obj α.left ⟶
              (abelianInverseImage i).obj G //
        ∀ {α β : CostructuredArrow (weaklyContractibleFreeAbelian Z) F}
          (f : α ⟶ β),
          (weaklyContractibleFreeAbelian Z).map f.left ≫ p β = p α }) :
    ∀ {α β : CostructuredArrow (weaklyContractibleFreeAbelian Z) F}
          (f : α ⟶ β),
          (weaklyContractibleLiftFreeAbelian i).map f.left ≫ ((abelianLowerShriekRepresentableHomEquiv i β.left G).symm (p.1 β)) = ((abelianLowerShriekRepresentableHomEquiv i α.left G).symm (p.1 α)) := sorry

private def abelianLowerShriekCoconeEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
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
      abelianLowerShriekCoconeEquiv_toFun_naturality i F G p⟩
  invFun q :=
    ⟨fun α =>
      (abelianLowerShriekRepresentableHomEquiv i α.left G).symm (q.1 α),
      abelianLowerShriekCoconeEquiv_invFun_naturality i F G q⟩
  left_inv p := by
    apply Subtype.ext
    funext α
    exact (abelianLowerShriekRepresentableHomEquiv i α.left G).symm_apply_apply (p.1 α)
  right_inv p := by
    apply Subtype.ext
    funext α
    exact (abelianLowerShriekRepresentableHomEquiv i α.left G).apply_symm_apply (p.1 α)

/-- Morphisms out of the colimit of `ℤ_{v(V)}` over an abelian sheaf identify
with cocones of those maps. -/
private def abelianLowerShriekColimitHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
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
private def abelianLowerShriekSourceColimitHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
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
def abelianLowerShriekHomEquiv (i : Z ⟶ X)
    [IsClosedImmersion i]
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

/-- The lower-shriek Hom equivalence commutes with precomposition in the source sheaf. -/
private theorem abelianLowerShriekHomEquiv_naturality_left_symm
    (i : Z ⟶ X) [IsClosedImmersion i]
    {F' F : Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}}
    {G : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}}
    (f : F' ⟶ F) (g : F ⟶ (abelianInverseImage i).obj G) :
    (abelianLowerShriekHomEquiv i F' G).symm (f ≫ g) =
      (abelianLowerShriek i).map f ≫ (abelianLowerShriekHomEquiv i F G).symm g := sorry

private theorem abelianLowerShriekHomEquiv_naturality_right
    (i : Z ⟶ X) [IsClosedImmersion i]
    {F : Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}}
    {G G' : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}}
    (f : (abelianLowerShriek i).obj F ⟶ G) (g : G ⟶ G') :
    abelianLowerShriekHomEquiv i F G' (f ≫ g) =
      abelianLowerShriekHomEquiv i F G f ≫ (abelianInverseImage i).map g := sorry

/-- Lower shriek is left adjoint to inverse image on abelian sheaves. -/
@[expose] def abelianLowerShriekAdjunction (i : Z ⟶ X)
    [IsClosedImmersion i] :
    abelianLowerShriek i ⊣ abelianInverseImage i :=
  Adjunction.mkOfHomEquiv
    { homEquiv := abelianLowerShriekHomEquiv i
      homEquiv_naturality_left_symm := by exact abelianLowerShriekHomEquiv_naturality_left_symm i
      homEquiv_naturality_right := by exact abelianLowerShriekHomEquiv_naturality_right i }

/-- The unit of abelian lower shriek is the unit of
`abelianLowerShriekAdjunction`. -/
theorem abelianLowerShriekAdjunction_unit (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}) :
    (abelianLowerShriekAdjunction i).unit.app F =
      (abelianLowerShriekHomEquiv i F ((abelianLowerShriek i).obj F))
        (𝟙 _) :=
  rfl

/-- The unit `id ⟶ i⁻¹ i_!` is an isomorphism. -/
instance abelianLowerShriek_unit_isIso (i : Z ⟶ X)
    [IsClosedImmersion i] :
    IsIso (abelianLowerShriekAdjunction i).unit := sorry

/-- Abelian lower shriek is fully faithful, as its adjunction unit is an
isomorphism. -/
@[expose] def abelianLowerShriekFullyFaithful (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (abelianLowerShriek i).FullyFaithful :=
  (abelianLowerShriekAdjunction i).fullyFaithfulLOfIsIsoUnit

/-- Small type-valued lower shriek, conjugated along affine ind-étale
restriction. -/
@[expose] def smallSheafLowerShriek (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf (topology Z) (Type (u + 1)) ⥤ Sheaf (topology X) (Type (u + 1)) :=
  affineIndEtaleRestriction Z ⋙ sheafLowerShriek i ⋙
    (affineIndEtaleInclusion X).sheafPushforwardCocontinuous (Type (u + 1))
      (affineIndEtaleTopology X) (topology X)

/-- Small type-valued lower shriek is restriction, app-site lower shriek, and
cocontinuous extension. -/
theorem smallSheafLowerShriek_def (i : Z ⟶ X)
    [IsClosedImmersion i] :
    smallSheafLowerShriek i =
      affineIndEtaleRestriction Z ⋙ sheafLowerShriek i ⋙
        (affineIndEtaleInclusion X).sheafPushforwardCocontinuous (Type (u + 1))
          (affineIndEtaleTopology X) (topology X) :=
  rfl

/-- Small abelian lower shriek, conjugated along affine ind-étale restriction. -/
@[expose] def smallAbelianLowerShriek (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf (topology Z) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology X) AddCommGrpCat.{u + 1} :=
  (affineIndEtaleInclusion Z).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (affineIndEtaleTopology Z) (topology Z) ⋙
    abelianLowerShriek i ⋙
    (affineIndEtaleInclusion X).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
      (affineIndEtaleTopology X) (topology X)

/-- Small abelian lower shriek is restriction, app-site lower shriek, and
cocontinuous extension. -/
theorem smallAbelianLowerShriek_def (i : Z ⟶ X)
    [IsClosedImmersion i] :
    smallAbelianLowerShriek i =
      (affineIndEtaleInclusion Z).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (affineIndEtaleTopology Z) (topology Z) ⋙
        abelianLowerShriek i ⋙
        (affineIndEtaleInclusion X).sheafPushforwardCocontinuous
          AddCommGrpCat.{u + 1} (affineIndEtaleTopology X) (topology X) :=
  rfl

/-- Lower shriek on the small pro-étale site is left adjoint to its
canonical inverse-image functor. -/
@[expose] def smallSheafLowerShriekAdjunction (i : Z ⟶ X)
    [IsClosedImmersion i] :
    smallSheafLowerShriek i ⊣ (smallProetalePullback i).sheafPullback (Type (u + 1))
      (topology X) (topology Z) :=
  (((AffineIndEtaleComparison.sheafEquivalence Z (Type (u + 1))).toAdjunction.comp
      (sheafLowerShriekAdjunction i)).comp
        (AffineIndEtaleComparison.sheafEquivalence X (Type (u + 1))).symm.toAdjunction).ofNatIsoRight
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (smallInverseImage_restrictionIso i) (AffineIndEtaleComparison.sheafEquivalence Z (Type (u + 1))).inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((smallProetalePullback i).sheafPullback (Type (u + 1))
      (topology X) (topology Z))
        (AffineIndEtaleComparison.sheafEquivalence Z (Type (u + 1))).unitIso.symm ≪≫
      Functor.rightUnitor _)

/-- The unit of lower shriek and inverse image on the small pro-étale site
is an isomorphism. -/
instance smallSheafLowerShriek_unit_isIso (i : Z ⟶ X)
    [IsClosedImmersion i] :
    IsIso (smallSheafLowerShriekAdjunction i).unit := sorry

/-- Lower shriek on the small pro-étale site is fully faithful. -/
@[expose] def smallSheafLowerShriekFullyFaithful (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (smallSheafLowerShriek i).FullyFaithful :=
  (smallSheafLowerShriekAdjunction i).fullyFaithfulLOfIsIsoUnit

/-- Lower shriek on the small pro-étale site is left adjoint to its
canonical inverse-image functor. -/
@[expose] def smallAbelianLowerShriekAdjunction (i : Z ⟶ X)
    [IsClosedImmersion i] :
    smallAbelianLowerShriek i ⊣ (smallProetalePullback i).sheafPullback AddCommGrpCat.{u + 1}
      (topology X) (topology Z) :=
  (((AffineIndEtaleComparison.sheafEquivalence Z AddCommGrpCat.{u + 1}).toAdjunction.comp
      (abelianLowerShriekAdjunction i)).comp
        (AffineIndEtaleComparison.sheafEquivalence X AddCommGrpCat.{u + 1}).symm.toAdjunction).ofNatIsoRight
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (smallAbelianInverseImage_restrictionIso i) (AffineIndEtaleComparison.sheafEquivalence Z AddCommGrpCat.{u + 1}).inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft ((smallProetalePullback i).sheafPullback AddCommGrpCat.{u + 1}
      (topology X) (topology Z))
        (AffineIndEtaleComparison.sheafEquivalence Z AddCommGrpCat.{u + 1}).unitIso.symm ≪≫
      Functor.rightUnitor _)

/-- The unit of lower shriek and inverse image on the small pro-étale site
is an isomorphism. -/
instance smallAbelianLowerShriek_unit_isIso (i : Z ⟶ X)
    [IsClosedImmersion i] :
    IsIso (smallAbelianLowerShriekAdjunction i).unit := sorry

/-- Lower shriek on the small pro-étale site is fully faithful. -/
@[expose] def smallAbelianLowerShriekFullyFaithful (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (smallAbelianLowerShriek i).FullyFaithful :=
  (smallAbelianLowerShriekAdjunction i).fullyFaithfulLOfIsIsoUnit

/-- Lower shriek along an affine closed immersion is full. -/
instance sheafLowerShriek_full (i : Z ⟶ X)
    [IsClosedImmersion i] : (sheafLowerShriek i).Full :=
  (sheafLowerShriekFullyFaithful i).full

/-- Lower shriek along an affine closed immersion is faithful. -/
instance sheafLowerShriek_faithful (i : Z ⟶ X)
    [IsClosedImmersion i] : (sheafLowerShriek i).Faithful :=
  (sheafLowerShriekFullyFaithful i).faithful

/-- Lower shriek along an affine closed immersion is full. -/
instance abelianLowerShriek_full (i : Z ⟶ X)
    [IsClosedImmersion i] : (abelianLowerShriek i).Full :=
  (abelianLowerShriekFullyFaithful i).full

/-- Lower shriek along an affine closed immersion is faithful. -/
instance abelianLowerShriek_faithful (i : Z ⟶ X)
    [IsClosedImmersion i] : (abelianLowerShriek i).Faithful :=
  (abelianLowerShriekFullyFaithful i).faithful

/-- Lower shriek along an affine closed immersion is full. -/
instance smallSheafLowerShriek_full (i : Z ⟶ X)
    [IsClosedImmersion i] : (smallSheafLowerShriek i).Full :=
  (smallSheafLowerShriekFullyFaithful i).full

/-- Lower shriek along an affine closed immersion is faithful. -/
instance smallSheafLowerShriek_faithful (i : Z ⟶ X)
    [IsClosedImmersion i] : (smallSheafLowerShriek i).Faithful :=
  (smallSheafLowerShriekFullyFaithful i).faithful

/-- Lower shriek along an affine closed immersion is full. -/
instance smallAbelianLowerShriek_full (i : Z ⟶ X)
    [IsClosedImmersion i] : (smallAbelianLowerShriek i).Full :=
  (smallAbelianLowerShriekFullyFaithful i).full

/-- Lower shriek along an affine closed immersion is faithful. -/
instance smallAbelianLowerShriek_faithful (i : Z ⟶ X)
    [IsClosedImmersion i] : (smallAbelianLowerShriek i).Faithful :=
  (smallAbelianLowerShriekFullyFaithful i).faithful

end AffineIndEtale

end AlgebraicGeometry.Scheme.ProEt
