module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import Mathlib.CategoryTheory.Category.Cat.Terminal
public import Mathlib.CategoryTheory.SingleObj

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Bicategory Pseudofunctor.StrongTrans

noncomputable section

universe u v

namespace AlgebraicGeometry

namespace FieldExtension.Galois

/-- The Galois group, viewed as a one-object category, acts contravariantly on the
field-extension base change through its canonical scheme automorphisms. -/
noncomputable def actionFunctor
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    SingleObj (Gal(K/k)) ⥤ Scheme.{u}ᵒᵖ where
  obj _ := .op (FieldExtension.baseChange k K f)
  map σ := (map k K f σ).op
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The action functor sends a Galois element to the corresponding
base-change automorphism. -/
theorem actionFunctor_map
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (σ : Gal(K/k)) :
    (actionFunctor k K f).map (SingleObj.toEnd (Gal(K/k)) σ) =
      (map k K f σ).op := sorry

end FieldExtension.Galois

namespace Scheme.QCoh.Galois

/-- A specified object of the chosen terminal category in `Cat`. -/
noncomputable def terminalPoint : (⊤_ Cat.{v, u}) :=
  (Limits.terminalIsTerminal.from
    (Cat.of (ShrinkHoms.{u} PUnit.{u + 1}) : Cat.{v, u})).toFunctor.obj
      (ShrinkHoms.toShrinkHoms PUnit.unit)

/-- The constant terminal-category pseudofunctor on the one-object Galois category. -/
def terminalPseudofunctor
    (k K : Type u) [Field k] [Field K] [Algebra k K] :
    LocallyDiscrete (SingleObj (Gal(K/k))) ⥤ᵖ Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun _ ↦ (⊤_ Cat))
    (fun _ ↦ 𝟙 _)
    (fun _ ↦ Iso.refl _)
    (fun _ _ ↦ (λ_ (𝟙 _)).symm)
    (fun _ _ _ ↦ sorry)
    (fun _ ↦ sorry)
    (fun _ ↦ sorry)

/-- The morphism in the locally discrete one-object category corresponding to a
Galois element. -/
def index
    (k K : Type u) [Field k] [Field K] [Algebra k K] (σ : Gal(K/k)) :
    (LocallyDiscrete.mk (SingleObj.star (Gal(K/k))) ⟶
      LocallyDiscrete.mk (SingleObj.star (Gal(K/k)))) :=
  (SingleObj.toEnd (Gal(K/k)) σ).toLoc

/-- Galois multiplication agrees with composition of the corresponding index
morphisms. -/
theorem index_mul
    (k K : Type u) [Field k] [Field K] [Algebra k K] (σ τ : Gal(K/k)) :
    index k K σ ≫ index k K τ = index k K (τ * σ) := sorry

/-- The pseudofunctorial action of `Gal(K/k)` on quasi-coherent modules over the
field-extension base change of `X`. -/
noncomputable def action
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    LocallyDiscrete (SingleObj (Gal(K/k))) ⥤ᵖ Cat :=
  (FieldExtension.Galois.actionFunctor k K f).toPseudofunctor.comp QCoh.pseudofunctor

/-- The action of `σ` on the unique fibre is pullback along the Galois-induced
automorphism `FieldExtension.Galois.map k K f σ`. -/
theorem action_map
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    ((action k K f).map (index k K σ)).toFunctor =
      QCoh.pullback (FieldExtension.Galois.map k K f σ) := sorry

/-- In the opposite scheme category, the base-change projection followed by a
Galois action morphism is again the base-change projection. -/
theorem projection_comp
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ : Gal(K/k)) :
    (FieldExtension.toSource k K f).op.toLoc ≫
        (FieldExtension.Galois.map k K f σ).op.toLoc =
      (FieldExtension.toSource k K f).op.toLoc := sorry

/-- The canonical comparison from pullback to `X_K` to its further pullback by
the Galois automorphism `f_σ`. -/
noncomputable def restrictionTransition
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (F : QCoh X) (σ : Gal(K/k)) :
    (QCoh.pullback (FieldExtension.toSource k K f)).obj F ≅
      (QCoh.pullback (FieldExtension.Galois.map k K f σ)).obj
        ((QCoh.pullback (FieldExtension.toSource k K f)).obj F) :=
  (Cat.Hom.toNatIso
    ((QCoh.pseudofunctor.map₂Iso (eqToIso (projection_comp k K f σ).symm)).trans
      (QCoh.pseudofunctor.mapComp
        (FieldExtension.toSource k K f).op.toLoc
        (FieldExtension.Galois.map k K f σ).op.toLoc))).app F

/-- The identity comparison for the Galois pullback action. -/
noncomputable def identityIso
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    QCoh.pullback (FieldExtension.Galois.map k K f 1) ≅
      𝟭 (QCoh (FieldExtension.baseChange k K f)) :=
  Cat.Hom.toNatIso
    ((action k K f).mapId (LocallyDiscrete.mk (SingleObj.star (Gal(K/k)))))

/-- The composition comparison identifies pullback by `f_(στ)` with pullback
first by `f_τ` and then by `f_σ`. -/
noncomputable def compositionIso
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (σ τ : Gal(K/k)) :
    QCoh.pullback (FieldExtension.Galois.map k K f (σ * τ)) ≅
      QCoh.pullback (FieldExtension.Galois.map k K f τ) ⋙
        QCoh.pullback (FieldExtension.Galois.map k K f σ) :=
  Cat.Hom.toNatIso
    (((action k K f).map₂Iso (eqToIso (index_mul k K τ σ).symm)).trans
      ((action k K f).mapComp (index k K τ) (index k K σ)))

/-- The category of Galois descent systems on the field-extension base change of `X`.
Its objects are pseudocones, hence a quasi-coherent module together with coherent
pullback isomorphisms indexed by `Gal(K/k)`. -/
noncomputable def DescentData
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) : Type (u + 1) :=
  Pseudofunctor.StrongTrans (terminalPseudofunctor k K) (action k K f)

/-- Galois descent systems carry the canonical category of strong transformations
and modifications. -/
instance descentDataCategory
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    Category (DescentData k K f) :=
  Pseudofunctor.StrongTrans.homCategory

namespace DescentData

/-- The quasi-coherent module underlying a Galois descent system. -/
noncomputable def underlying
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    (D : DescentData k K f) : QCoh (FieldExtension.baseChange k K f) :=
  (D.app (LocallyDiscrete.mk (SingleObj.star (Gal(K/k))))).toFunctor.obj
    terminalPoint

/-- The transition isomorphism `φ_σ : 𝒜 ≅ f_σ^* 𝒜` carried by a Galois
descent system. -/
noncomputable def transitionIso
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    (D : DescentData k K f) (σ : Gal(K/k)) :
    underlying k K D ≅
      (QCoh.pullback (FieldExtension.Galois.map k K f σ)).obj (underlying k K D) :=
  (Cat.Hom.toNatIso
    (D.naturality (index k K σ))).app
    terminalPoint

/-- The morphism of underlying quasi-coherent modules carried by a morphism of
Galois descent systems. -/
noncomputable def underlyingMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    {D E : DescentData k K f} (a : D ⟶ E) :
    underlying k K D ⟶ underlying k K E :=
  (a.as.app (LocallyDiscrete.mk (SingleObj.star (Gal(K/k))))).toNatTrans.app
    terminalPoint

/-- The identity transition is the inverse of the action's identity comparison. -/
theorem transitionIso_one
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    (D : DescentData k K f) :
    (transitionIso k K D 1).hom ≫
        (identityIso k K f).hom.app (underlying k K D) =
      𝟙 (underlying k K D) := sorry

/-- The transition isomorphisms satisfy the Galois cocycle, with the canonical
pseudofunctor composition comparison made explicit. -/
theorem transitionIso_mul
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    (D : DescentData k K f) (σ τ : Gal(K/k)) :
    (transitionIso k K D (σ * τ)).hom ≫
        (compositionIso k K f σ τ).hom.app (underlying k K D) =
      (transitionIso k K D σ).hom ≫
        (QCoh.pullback (FieldExtension.Galois.map k K f σ)).map
          (transitionIso k K D τ).hom := sorry

/-- Morphisms of Galois descent systems commute with every transition
isomorphism. -/
theorem hom_compatibility
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    {D E : DescentData k K f} (a : D ⟶ E) (σ : Gal(K/k)) :
    underlyingMap k K a ≫ (transitionIso k K E σ).hom =
      (transitionIso k K D σ).hom ≫
        (QCoh.pullback (FieldExtension.Galois.map k K f σ)).map
          (underlyingMap k K a) := sorry

end DescentData

/-- The canonical Galois descent system obtained by restricting a quasi-coherent
module from `X` to its field-extension base change. -/
noncomputable def restrictionObj
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (F : QCoh X) :
    DescentData k K f where
  app _ := Cat.Hom.ofFunctor <|
    (Functor.const (⊤_ Cat)).obj
      ((QCoh.pullback (FieldExtension.toSource k K f)).obj F)
  naturality σ := Cat.Hom.isoMk <| NatIso.ofComponents
    (fun _ ↦ restrictionTransition k K f F σ.as) (fun _ ↦ sorry)
  naturality_naturality := sorry
  naturality_id := sorry
  naturality_comp := sorry

/-- Restriction carries a morphism on `X` to the compatible morphism of its
canonical Galois descent systems. -/
noncomputable def restrictionMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    {F H : QCoh X} (a : F ⟶ H) :
    restrictionObj k K f F ⟶ restrictionObj k K f H where
  as :=
    { app := fun _ ↦ Cat.Hom₂.ofNatTrans
        { app := fun _ ↦
            (QCoh.pullback (FieldExtension.toSource k K f)).map a
          naturality := fun _ _ g ↦ sorry }
      naturality := fun _ ↦ sorry }

/-- Restriction from quasi-coherent modules on `X` to Galois descent systems on
the field-extension base change. -/
noncomputable def restriction
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    QCoh X ⥤ DescentData k K f where
  obj := restrictionObj k K f
  map := restrictionMap k K f
  map_id := sorry
  map_comp := sorry

namespace restriction

/-- The underlying object of the canonical restricted system is ordinary
pullback along `X_K ⟶ X`. -/
theorem obj_underlying
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (F : QCoh X) :
    DescentData.underlying k K ((restriction k K f).obj F) =
      (QCoh.pullback (FieldExtension.toSource k K f)).obj F := sorry

/-- The transition of a restricted object is the canonical pullback comparison. -/
theorem obj_transitionIso
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (F : QCoh X) (σ : Gal(K/k)) :
    DescentData.transitionIso k K ((restriction k K f).obj F) σ =
      restrictionTransition k K f F σ := sorry

/-- Finite Galois fpqc descent makes the restriction functor an equivalence. -/
instance isEquivalence
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) :
    (restriction k K f).IsEquivalence := sorry

end restriction

end Scheme.QCoh.Galois

end AlgebraicGeometry
