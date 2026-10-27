/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import ReasLib.CategoryTheory.Sites.Sheaf.Hom
public import ReasLib.CategoryTheory.Sites.Descent.Slice

/-!
# Representable descent on a subcanonical site

The glued sheaf is the coequalizer of the two maps from the coproduct of pairwise-overlap
representables to the coproduct of the local representables.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.GrothendieckTopology.RepresentableDescent

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (J : GrothendieckTopology C) [J.Subcanonical]
variable {S : C} {I : Type (max u v)} {X : I → C} (p : ∀ i, X i ⟶ S)

/-- Binary products in a slice are the pullbacks of their structure morphisms. -/
instance overHasBinaryProducts : HasBinaryProducts (Over S) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

/-- A sheaf is locally representable along `p` when its product with each representable
`h_(X i)` is representable on the slice over `S`. -/
def locallyRepresentableAlong (p : ∀ i, X i ⟶ S) :
    ObjectProperty (Sheaf (J.over S) (Type (max u v))) :=
  fun F ↦ ∀ i, ((J.over S).uliftYoneda.{max u v}).essImage
    (Limits.prod ((J.over S).uliftYoneda.{max u v}.obj (Over.mk (p i))) F)

/-- Membership in `locallyRepresentableAlong J p` is the componentwise representability of
the products with the covering representables. -/
theorem mem_locallyRepresentableAlong_iff
    (F : Sheaf (J.over S) (Type (max u v))) :
    locallyRepresentableAlong J p F ↔
      ∀ i, ((J.over S).uliftYoneda.{max u v}).essImage
        (Limits.prod ((J.over S).uliftYoneda.{max u v}.obj (Over.mk (p i))) F) := sorry

/-- The full subcategory of sheaves locally representable along `p`. -/
abbrev LocallyRepresentableAlong :=
  (locallyRepresentableAlong J p).FullSubcategory

/-- The object of `C` underlying the overlap of `X i` and `X j` over `S`. -/
abbrev overlapBaseObject (i j : I) : C := Limits.pullback (p i) (p j)

/-- The structural arrow from the overlap of `X i` and `X j` to `S`. -/
abbrev overlapToBase (i j : I) : overlapBaseObject p i j ⟶ S :=
  pullback.fst (p i) (p j) ≫ p i

/-- The second projection of an overlap has the same composite to the base as the first. -/
theorem overlap_snd_comp (i j : I) :
    pullback.snd (p i) (p j) ≫ p j = overlapToBase p i j := sorry

/-- The first projection of an overlap has the defining composite to the base. -/
theorem overlap_fst_comp (i j : I) :
    pullback.fst (p i) (p j) ≫ p i = overlapToBase p i j := sorry

/-- The object over `S` represented by the `i`th component of a slice descent datum. -/
def localObject (D : Over.pseudofunctor.DescentData p) (i : I) : Over S :=
  (Over.map (p i)).obj (D.obj i)

/-- The left component of a descent datum, restricted to the overlap and viewed over `S`. -/
def overlapObject (D : Over.pseudofunctor.DescentData p) (i j : I) : Over S :=
  (Over.map (overlapToBase p i j)).obj
    ((Over.pullback (pullback.fst (p i) (p j))).obj (D.obj i))

/-- The overlap projection to the left local object commutes with the structure maps to `S`. -/
theorem overlapToLeft_comm (D : Over.pseudofunctor.DescentData p) (i j : I) :
    pullback.fst (D.obj i).hom (pullback.fst (p i) (p j)) ≫
        (localObject p D i).hom = (overlapObject p D i j).hom := sorry

/-- The canonical map from the overlap object to the left local object. -/
def overlapToLeft (D : Over.pseudofunctor.DescentData p) (i j : I) :
    overlapObject p D i j ⟶ localObject p D i :=
  Over.homMk (pullback.fst (D.obj i).hom (pullback.fst (p i) (p j)))
    (overlapToLeft_comm p D i j)

/-- The descent comparison on an overlap, followed by its projection to the right component,
commutes with the structure maps to `S`. -/
theorem overlapToRight_comm (D : Over.pseudofunctor.DescentData p) (i j : I) :
    ((D.hom (overlapToBase p i j) (pullback.fst (p i) (p j))
        (pullback.snd (p i) (p j)) (overlap_fst_comp p i j)
          (overlap_snd_comp p i j)).left ≫
        pullback.fst (D.obj j).hom (pullback.snd (p i) (p j))) ≫
        (localObject p D j).hom = (overlapObject p D i j).hom := sorry

/-- The canonical map from the overlap object to the right local object, using the descent
comparison. -/
def overlapToRight (D : Over.pseudofunctor.DescentData p) (i j : I) :
    overlapObject p D i j ⟶ localObject p D j :=
  Over.homMk
    ((D.hom (overlapToBase p i j) (pullback.fst (p i) (p j))
        (pullback.snd (p i) (p j)) (overlap_fst_comp p i j)
          (overlap_snd_comp p i j)).left ≫
      pullback.fst (D.obj j).hom (pullback.snd (p i) (p j)))
    (overlapToRight_comm p D i j)

/-- The representable sheaf associated to the `i`th local object of a descent datum. -/
abbrev localSheaf (D : Over.pseudofunctor.DescentData p) (i : I) :
    Sheaf (J.over S) (Type (max u v)) :=
  (J.over S).uliftYoneda.{max u v}.obj (localObject p D i)

/-- The representable sheaf associated to a pairwise overlap object. -/
abbrev overlapSheaf (D : Over.pseudofunctor.DescentData p) (ij : I × I) :
    Sheaf (J.over S) (Type (max u v)) :=
  (J.over S).uliftYoneda.{max u v}.obj (overlapObject p D ij.1 ij.2)

/-- The first relation map in the representable coequalizer attached to descent data. -/
def relationFst (D : Over.pseudofunctor.DescentData p) :
    ∐ (overlapSheaf J p D) ⟶ ∐ (localSheaf J p D) :=
  Sigma.desc (fun ij ↦
    (J.over S).uliftYoneda.{max u v}.map (overlapToLeft p D ij.1 ij.2) ≫
      Sigma.ι (localSheaf J p D) ij.1)

/-- The second relation map in the representable coequalizer attached to descent data. -/
def relationSnd (D : Over.pseudofunctor.DescentData p) :
    ∐ (overlapSheaf J p D) ⟶ ∐ (localSheaf J p D) :=
  Sigma.desc (fun ij ↦
    (J.over S).uliftYoneda.{max u v}.map (overlapToRight p D ij.1 ij.2) ≫
      Sigma.ι (localSheaf J p D) ij.2)

/-- The sheaf glued from representable descent data, defined as the coequalizer of the overlap relation. -/
def gluedSheaf (D : Over.pseudofunctor.DescentData p) :
    Sheaf (J.over S) (Type (max u v)) :=
  coequalizer (relationFst J p D) (relationSnd J p D)

/-- A morphism of descent data induces maps between its local representable sheaves. -/
def localMap {D E : Over.pseudofunctor.DescentData p} (φ : D ⟶ E) (i : I) :
    localSheaf J p D i ⟶ localSheaf J p E i :=
  (J.over S).uliftYoneda.{max u v}.map ((Over.map (p i)).map (φ.hom i))

/-- The coproduct of the local maps coequalizes the two overlap relations. -/
theorem localMap_coequalizes {D E : Over.pseudofunctor.DescentData p} (φ : D ⟶ E) :
    relationFst J p D ≫ Limits.Sigma.map (localMap J p φ) ≫
        coequalizer.π (relationFst J p E) (relationSnd J p E) =
      relationSnd J p D ≫ Limits.Sigma.map (localMap J p φ) ≫
        coequalizer.π (relationFst J p E) (relationSnd J p E) := sorry

/-- The morphism of glued sheaves induced by a morphism of descent data. -/
def gluedMap {D E : Over.pseudofunctor.DescentData p} (φ : D ⟶ E) :
    gluedSheaf J p D ⟶ gluedSheaf J p E :=
  coequalizer.desc
    (Limits.Sigma.map (localMap J p φ) ≫
      coequalizer.π (relationFst J p E) (relationSnd J p E))
    (localMap_coequalizes J p φ)

/-- The glued map associated to an identity descent morphism is the identity. -/
theorem gluedMap_id (D : Over.pseudofunctor.DescentData p) :
    gluedMap J p (𝟙 D) = 𝟙 (gluedSheaf J p D) := sorry

/-- Glued maps preserve composition of descent morphisms. -/
theorem gluedMap_comp {D E F : Over.pseudofunctor.DescentData p}
    (φ : D ⟶ E) (ψ : E ⟶ F) :
    gluedMap J p (φ ≫ ψ) = gluedMap J p φ ≫ gluedMap J p ψ := sorry

/-- The glued sheaf is locally representable along the covering family. -/
theorem gluedSheaf_locallyRepresentable
    (hcover : Sieve.ofArrows X p ∈ J S) (D : Over.pseudofunctor.DescentData p) :
    locallyRepresentableAlong J p (gluedSheaf J p D) := sorry

/-- Explicit representable descent glues slice-object descent data to locally representable
sheaves on the slice site. -/
def glue (hcover : Sieve.ofArrows X p ∈ J S) :
    Over.pseudofunctor.DescentData p ⥤ LocallyRepresentableAlong J p where
  obj D := ⟨gluedSheaf J p D, gluedSheaf_locallyRepresentable J p hcover D⟩
  map φ := ObjectProperty.homMk (gluedMap J p φ)
  map_id D := congrArg ObjectProperty.homMk (gluedMap_id J p D)
  map_comp φ ψ := congrArg ObjectProperty.homMk (gluedMap_comp J p φ ψ)

/-- Representable gluing is an equivalence for a covering family. -/
instance glueIsEquivalence (hcover : Sieve.ofArrows X p ∈ J S) :
    Functor.IsEquivalence (glue J p hcover) := sorry

/-- The product of a local descent object with the `i`th covering object. -/
abbrev localPair (D : Over.pseudofunctor.DescentData p) (i j : I) : Over S :=
  Limits.prod (localObject p D j) (Over.mk (p i))

/-- The projection of a local pair to the `i`th covering object. -/
abbrev localPairToCover (D : Over.pseudofunctor.DescentData p) (i j : I) :
    (localPair p D i j).left ⟶ X i :=
  (prod.snd : localPair p D i j ⟶ Over.mk (p i)).left

/-- The projection of a local pair through the `j`th local descent object. -/
abbrev localPairToLocalBase (D : Over.pseudofunctor.DescentData p) (i j : I) :
    (localPair p D i j).left ⟶ X j :=
  (prod.fst : localPair p D i j ⟶ localObject p D j).left ≫ (D.obj j).hom

/-- The first local-pair projection has the required composite to the base. -/
theorem localPairToCover_comp (D : Over.pseudofunctor.DescentData p) (i j : I) :
    localPairToCover p D i j ≫ p i = (localPair p D i j).hom := sorry

/-- The second local-pair projection has the required composite to the base. -/
theorem localPairToLocalBase_comp
    (D : Over.pseudofunctor.DescentData p) (i j : I) :
    localPairToLocalBase p D i j ≫ p j = (localPair p D i j).hom := sorry

/-- The first projection of a local pair defines a morphism over the `j`th covering object. -/
theorem localPairSectionOver_comm
    (D : Over.pseudofunctor.DescentData p) (i j : I) :
    (prod.fst : localPair p D i j ⟶ localObject p D j).left ≫ (D.obj j).hom =
      ((Over.map (localPairToLocalBase p D i j)).obj
        (Over.mk (𝟙 (localPair p D i j).left))).hom := sorry

/-- The tautological section of the pullback of the `j`th local descent object. -/
def localPairSectionOver
    (D : Over.pseudofunctor.DescentData p) (i j : I) :
    (Over.map (localPairToLocalBase p D i j)).obj
        (Over.mk (𝟙 (localPair p D i j).left)) ⟶ D.obj j :=
  Over.homMk (prod.fst : localPair p D i j ⟶ localObject p D j).left
    (localPairSectionOver_comm p D i j)

/-- Descent transports the tautological `j`th section to an `i`th local section. -/
noncomputable def localPairToDescentObject
    (D : Over.pseudofunctor.DescentData p) (i j : I) :
    (localPair p D i j).left ⟶ (D.obj i).left :=
  (((Over.mapPullbackAdj (localPairToCover p D i j)).homEquiv
      (Over.mk (𝟙 (localPair p D i j).left)) (D.obj i)).symm
    ((Over.mapPullbackAdj (localPairToLocalBase p D i j)).homEquiv
        (Over.mk (𝟙 (localPair p D i j).left)) (D.obj j)
        (localPairSectionOver p D i j) ≫
      (D.iso (localPair p D i j).hom
        (localPairToCover p D i j) (localPairToLocalBase p D i j)
        (localPairToCover_comp p D i j) (localPairToLocalBase_comp p D i j)).inv)).left

/-- The transported local section commutes with the maps to `S`. -/
theorem localPairToDescentObject_comm
    (D : Over.pseudofunctor.DescentData p) (i j : I) :
    localPairToDescentObject p D i j ≫ (localObject p D i).hom =
      (localPair p D i j).hom := sorry

/-- A pair consisting of an `i`th-cover map and a `j`th local section transports to the
`i`th local descent object. -/
noncomputable def localPairTransition
    (D : Over.pseudofunctor.DescentData p) (i j : I) :
    localPair p D i j ⟶ localObject p D i :=
  Over.homMk (localPairToDescentObject p D i j)
    (localPairToDescentObject_comm p D i j)

/-- The sheaf morphism induced by the local-pair descent transition. -/
noncomputable def localPairSheafMap
    (D : Over.pseudofunctor.DescentData p) (i j : I) :
    Limits.prod (localSheaf J p D j)
        ((J.over S).uliftYoneda.{max u v}.obj (Over.mk (p i))) ⟶
      localSheaf J p D i :=
  (PreservesLimitPair.iso
      (J.over S).uliftYoneda.{max u v} (localObject p D j) (Over.mk (p i))).inv ≫
    (J.over S).uliftYoneda.{max u v}.map (localPairTransition p D i j)

/-- Currying the local-pair transition gives a map from each local representable into the
internal Hom from the `i`th covering representable. -/
noncomputable def localToHom
    (D : Over.pseudofunctor.DescentData p) (i j : I) :
    localSheaf J p D j ⟶
      sheafHom ((J.over S).uliftYoneda.{max u v}.obj (Over.mk (p i)))
        (localSheaf J p D i) :=
  Sheaf.Hom.curryEquiv (localSheaf J p D j)
    ((J.over S).uliftYoneda.{max u v}.obj (Over.mk (p i))) (localSheaf J p D i)
      (localPairSheafMap J p D i j)

/-- The local-to-internal-Hom maps respect the overlap relation. -/
theorem localToHom_coequalizes
    (D : Over.pseudofunctor.DescentData p) (i : I) :
    relationFst J p D ≫ Sigma.desc (fun j ↦ localToHom J p D i j) =
      relationSnd J p D ≫ Sigma.desc (fun j ↦ localToHom J p D i j) := sorry

/-- The descent transitions induce a map from the glued sheaf to the local internal Hom. -/
noncomputable def gluedToHom
    (D : Over.pseudofunctor.DescentData p) (i : I) :
    gluedSheaf J p D ⟶
      sheafHom ((J.over S).uliftYoneda.{max u v}.obj (Over.mk (p i)))
        (localSheaf J p D i) :=
  coequalizer.desc (Sigma.desc (fun j ↦ localToHom J p D i j))
    (localToHom_coequalizes J p D i)

/-- The forward local comparison evaluates the descent transition on the product of the
covering representable with the glued sheaf. -/
noncomputable def productComparisonHom (hcover : Sieve.ofArrows X p ∈ J S)
    (D : Over.pseudofunctor.DescentData p) (i : I) :
    Limits.prod ((J.over S).uliftYoneda.{max u v}.obj (Over.mk (p i)))
        ((glue J p hcover).obj D).obj ⟶
      (J.over S).uliftYoneda.{max u v}.obj (localObject p D i) :=
  (prod.braiding _ _).hom ≫
    (Sheaf.Hom.curryEquiv (gluedSheaf J p D)
      ((J.over S).uliftYoneda.{max u v}.obj (Over.mk (p i))) (localSheaf J p D i)).symm
        (gluedToHom J p D i)

/-- The `i`th local descent object maps canonically to the `i`th covering object. -/
def localObjectToCover (D : Over.pseudofunctor.DescentData p) (i : I) :
    localObject p D i ⟶ Over.mk (p i) :=
  Over.homMk (D.obj i).hom

/-- The inverse local comparison pairs the structural map to the covering representable with
the canonical map into the defining coequalizer. -/
noncomputable def productComparisonInv (D : Over.pseudofunctor.DescentData p) (i : I) :
    (J.over S).uliftYoneda.{max u v}.obj (localObject p D i) ⟶
      Limits.prod ((J.over S).uliftYoneda.{max u v}.obj (Over.mk (p i)))
        (gluedSheaf J p D) :=
  prod.lift
    ((J.over S).uliftYoneda.{max u v}.map (localObjectToCover p D i))
    (Sigma.ι (localSheaf J p D) i ≫ coequalizer.π (relationFst J p D) (relationSnd J p D))

/-- The forward and inverse local comparison maps compose to the identity on the product. -/
theorem productComparison_hom_inv_id (hcover : Sieve.ofArrows X p ∈ J S)
    (D : Over.pseudofunctor.DescentData p) (i : I) :
    productComparisonHom J p hcover D i ≫ productComparisonInv J p D i = 𝟙 _ := sorry

/-- The inverse and forward local comparison maps compose to the identity on the local
representable. -/
theorem productComparison_inv_hom_id (hcover : Sieve.ofArrows X p ∈ J S)
    (D : Over.pseudofunctor.DescentData p) (i : I) :
    productComparisonInv J p D i ≫ productComparisonHom J p hcover D i = 𝟙 _ := sorry

/-- On each covering member, the product of the glued sheaf with its representable is
isomorphic to the representable sheaf of the corresponding local object. -/
noncomputable def productIso (hcover : Sieve.ofArrows X p ∈ J S)
    (D : Over.pseudofunctor.DescentData p) (i : I) :
    Limits.prod ((J.over S).uliftYoneda.{max u v}.obj (Over.mk (p i)))
        ((glue J p hcover).obj D).obj ≅
      (J.over S).uliftYoneda.{max u v}.obj (localObject p D i) where
  hom := productComparisonHom J p hcover D i
  inv := productComparisonInv J p D i
  hom_inv_id := productComparison_hom_inv_id J p hcover D i
  inv_hom_id := productComparison_inv_hom_id J p hcover D i

/-- The forward map of `productIso` is the explicit descent comparison. -/
theorem productIso_hom (hcover : Sieve.ofArrows X p ∈ J S)
    (D : Over.pseudofunctor.DescentData p) (i : I) :
    (productIso J p hcover D i).hom = productComparisonHom J p hcover D i := sorry

/-- The inverse map of `productIso` is the local inclusion into the glued coequalizer. -/
theorem productIso_inv (hcover : Sieve.ofArrows X p ∈ J S)
    (D : Over.pseudofunctor.DescentData p) (i : I) :
    (productIso J p hcover D i).inv = productComparisonInv J p D i := sorry

/-- The sheaf glued from descent data is representable exactly when that descent datum is
effective. -/
theorem representable_iff_effective (hcover : Sieve.ofArrows X p ∈ J S)
    (D : Over.pseudofunctor.DescentData p) :
    ((J.over S).uliftYoneda.{max u v}).essImage ((glue J p hcover).obj D).obj ↔
      Over.DescentData.IsEffective X p D := sorry

end CategoryTheory.GrothendieckTopology.RepresentableDescent
