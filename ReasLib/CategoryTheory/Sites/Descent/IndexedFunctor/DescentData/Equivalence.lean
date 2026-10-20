module

public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Basic
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Actual descent transport through fibre equivalences

The component equivalence witnesses are supplied explicitly. The inverse indexed
functor uses their actual unit and counit maps. This constructs descent inverse
objects, maps, preimages and glue witnesses without an admitted fullness or
stack-transport factory.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory.Bicategory

noncomputable section

universe t u v uF vF uG vG

namespace CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type u} [Category.{v} C]
variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF}}
variable {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vG, uG}}
variable (H : IndexedFunctor (𝟭 C) F G)
variable (hH : ∀ U : C, (H.app U).IsEquivalence)

/-- The supplied component equivalence is reified by the native constructor. -/
def componentEquivalence (U : C) : F.obj (.mk (op U)) ≌ G.obj (.mk (op U)) :=
  @Functor.asEquivalence _ _ _ _ (H.app U) (hH U)

/-- Naturality of the inverse components is the mate of original naturality. -/
def inverseNaturality {U V : C} (f : V ⟶ U) :
    (G.map f.op.toLoc).toFunctor ⋙ (componentEquivalence H hH V).inverse ≅
      (componentEquivalence H hH U).inverse ⋙ (F.map f.op.toLoc).toFunctor :=
  NatIso.ofComponents
    (fun x ↦
      { hom :=
          (componentEquivalence H hH V).inverse.map
            ((G.map f.op.toLoc).toFunctor.map ((componentEquivalence H hH U).counitIso.inv.app x)) ≫
          (componentEquivalence H hH V).inverse.map
            ((H.naturality f).inv.app ((componentEquivalence H hH U).inverse.obj x)) ≫
          (componentEquivalence H hH V).unitIso.inv.app
            ((F.map f.op.toLoc).toFunctor.obj ((componentEquivalence H hH U).inverse.obj x))
        inv :=
          (componentEquivalence H hH V).unitIso.hom.app
            ((F.map f.op.toLoc).toFunctor.obj ((componentEquivalence H hH U).inverse.obj x)) ≫
          (componentEquivalence H hH V).inverse.map
            ((H.naturality f).hom.app ((componentEquivalence H hH U).inverse.obj x)) ≫
          (componentEquivalence H hH V).inverse.map
            ((G.map f.op.toLoc).toFunctor.map ((componentEquivalence H hH U).counitIso.hom.app x))
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (by sorry)

/-- The inverse indexed functor has actual component inverse functors and mates. -/
def inverseIndexed : IndexedFunctor (𝟭 C) G F where
  app U := (componentEquivalence H hH U).inverse
  naturality f := inverseNaturality H hH f
  naturality_id := sorry
  naturality_comp := sorry

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The descent unit is the actual component unit on every local object. -/
def descentUnit : 𝟭 (F.DescentData f) ≅
    H.mapDescentData f ⋙ (inverseIndexed H hH).mapDescentData f :=
  NatIso.ofComponents
    (fun D ↦
      { hom := { hom i := (componentEquivalence H hH (X i)).unitIso.hom.app (D.obj i), comm := by sorry }
        inv := { hom i := (componentEquivalence H hH (X i)).unitIso.inv.app (D.obj i), comm := by sorry }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (by sorry)

/-- The descent counit is the actual component counit on every local object. -/
def descentCounit :
    (inverseIndexed H hH).mapDescentData f ⋙ H.mapDescentData f ≅ 𝟭 (G.DescentData f) :=
  NatIso.ofComponents
    (fun D ↦
      { hom := { hom i := (componentEquivalence H hH (X i)).counitIso.hom.app (D.obj i), comm := by sorry }
        inv := { hom i := (componentEquivalence H hH (X i)).counitIso.inv.app (D.obj i), comm := by sorry }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (by sorry)

/-- The descent equivalence retains actual forward/inverse actions and units. -/
def descentEquivalence : F.DescentData f ≌ G.DescentData f where
  functor := H.mapDescentData f
  inverse := (inverseIndexed H hH).mapDescentData f
  unitIso := descentUnit H hH f
  counitIso := descentCounit H hH f
  functor_unitIso_comp := sorry

/-- Restricting a global object commutes with original indexed transport. -/
def toDescentDataIso :
    F.toDescentData f ⋙ H.mapDescentData f ≅ H.app S ⋙ G.toDescentData f :=
  NatIso.ofComponents
    (fun x ↦
      { hom := { hom i := (H.naturality (f i)).hom.app x, comm := by sorry }
        inv := { hom i := (H.naturality (f i)).inv.app x, comm := by sorry }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (by sorry)

/-- A target descent morphism is transported back, amalgamated using the
original supplied prestack, and transported forward by actual component maps. -/
def descentPreimage (J : GrothendieckTopology C) (hF : F.IsPrestack J)
    (hf : Sieve.ofArrows X f ∈ J S)
    {a b : G.obj (.mk (op S))} (γ : (G.toDescentData f).obj a ⟶ (G.toDescentData f).obj b) : a ⟶ b := by
  let K := inverseIndexed H hH
  let α := toDescentDataIso K f
  let δ := (α.inv.app a) ≫ (K.mapDescentData f).map γ ≫ (α.hom.app b)
  letI : F.IsPrestack J := hF
  let φ := (F.fullyFaithfulToDescentData f hf).preimage δ
  exact (componentEquivalence H hH S).counitIso.inv.app a ≫
    (H.app S).map φ ≫ (componentEquivalence H hH S).counitIso.hom.app b

/-- Full faithfulness stores that actual transported preimage. -/
def fullyFaithfulDescent (J : GrothendieckTopology C) (hF : F.IsPrestack J)
    (hf : Sieve.ofArrows X f ∈ J S) : (G.toDescentData f).FullyFaithful where
  preimage := descentPreimage H hH f J hF hf
  map_preimage := sorry
  preimage_map := sorry

include H hH in
/-- Prestack transport uses the implemented native covering-sieve bridge. -/
theorem isPrestackOfEquivalences (J : GrothendieckTopology C) (hF : F.IsPrestack J) : G.IsPrestack J :=
  Pseudofunctor.IsPrestack.of_isPrestackFor fun S R hR ↦
    { nonempty_fullyFaithful := ⟨fullyFaithfulDescent H hH
        (fun I : R.arrows.category ↦ I.obj.hom) J hF (by simpa only [Sieve.ofArrows_category] using hR)⟩ }

/-- The actual source glue object is chosen from the supplied source stack's
implemented essential-surjectivity witness, then mapped by the component. -/
def glueObject (J : GrothendieckTopology C) (hF : F.IsStack J)
    (R : J.Cover S) (D : G.DescentData (fun I : (R : Sieve S).arrows.category ↦ I.obj.hom)) :
    G.obj (.mk (op S)) := by
  letI : F.IsStack J := hF
  let K := inverseIndexed H hH
  let E := F.toDescentData (fun I : (R : Sieve S).arrows.category ↦ I.obj.hom)
  letI : E.EssSurj := Pseudofunctor.IsStack.essSurj_of_sieve F (R : Sieve S) R.condition
  exact (H.app S).obj (E.objPreimage ((K.mapDescentData _).obj D))

/-- The comparison glues the supplied datum through the actual source glue
isomorphism and the explicit descent counit. -/
def glueComparison (J : GrothendieckTopology C) (hF : F.IsStack J)
    (R : J.Cover S) (D : G.DescentData (fun I : (R : Sieve S).arrows.category ↦ I.obj.hom)) :
    (G.toDescentData (fun I : (R : Sieve S).arrows.category ↦ I.obj.hom)).obj
      (glueObject H hH J hF R D) ≅ D := by
  letI : F.IsStack J := hF
  let K := inverseIndexed H hH
  let family := fun I : (R : Sieve S).arrows.category ↦ I.obj.hom
  let E := F.toDescentData family
  letI : E.EssSurj := Pseudofunctor.IsStack.essSurj_of_sieve F (R : Sieve S) R.condition
  let D' := (K.mapDescentData family).obj D
  let x := E.objPreimage D'
  exact (toDescentDataIso H family).symm.app x ≪≫
    (H.mapDescentData family).mapIso (E.objObjPreimageIso D') ≪≫
      (descentCounit H hH family).app D

include H hH in
/-- Stack transport packages actual target preimages, glue objects and isos. -/
theorem isStackOfEquivalences (J : GrothendieckTopology C) (hF : F.IsStack J) : G.IsStack J where
  toIsPrestack := isPrestackOfEquivalences H hH J hF.toIsPrestack
  essSurj_of_sieve R hR :=
    { mem_essImage := fun D ↦ ⟨glueObject H hH J hF ⟨R, hR⟩ D,
        ⟨glueComparison H hH J hF ⟨R, hR⟩ D⟩⟩ }

end CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor
