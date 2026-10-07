module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap61.Lemma_61_12_21_AffineIndEtale
public import stacks_project.Chap61.Lemma_61_7_7_Category

/-!
# Affine ind-étale objects as opposite ind-étale algebras

Global sections send affine ind-étale objects of an affine scheme `S` to
ind-étale `Γ(S, ⊤)`-algebras. Spectra of such algebras recover objects of
the affine ind-étale site. Along a closed immersion of affines, the kernel of
the map on global sections identifies `Γ(Z, ⊤)` with a quotient of `Γ(X, ⊤)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open Opposite
open AlgebraicGeometry
open CommAlgCat

noncomputable section

universe u

namespace CommAlgCat.IndEtale

/-- Transport the `R`-algebra structure along a ring equivalence `R ≃+* S`. -/
@[reducible]
def algebraCompRingEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (A : Type u) [CommRing A] [Algebra R A] : Algebra S A :=
  ((algebraMap R A).comp e.symm.toRingHom).toAlgebra

/-- The structure map of `algebraCompRingEquiv` is `algebraMap R A` after `e.symm`. -/
theorem algebraCompRingEquiv_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (A : Type u) [CommRing A] [Algebra R A] :
    @algebraMap S A _ _ (algebraCompRingEquiv e A) =
      (algebraMap R A).comp e.symm.toRingHom := sorry

/-- An `R`-algebra map remains an `S`-algebra map after `algebraCompRingEquiv`. -/
def reindexAlgHom {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) :
    @AlgHom S A B _ _ _ (algebraCompRingEquiv e A) (algebraCompRingEquiv e B) :=
  @AlgHom.mk S A B _ _ _ (algebraCompRingEquiv e A) (algebraCompRingEquiv e B)
    f.toRingHom sorry

/-- Reindexing along a ring equivalence preserves ind-étaleness. -/
theorem reindex_obj_indEtale {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (C : IndEtale.{u} R) :
    (@algebraMap S C _ _ (algebraCompRingEquiv e C)).IndEtale := sorry

/-- Reindex ind-étale algebras along a ring equivalence, keeping the same carrier. -/
def reindex {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    IndEtale.{u} R ⥤ IndEtale.{u} S where
  obj C :=
    @of S _ C _ (algebraCompRingEquiv e C) (reindex_obj_indEtale e C)
  map {C D} f :=
    @ofHom S _ C D _ _ (algebraCompRingEquiv e C) (algebraCompRingEquiv e D)
      (reindex_obj_indEtale e C) (reindex_obj_indEtale e D)
      (reindexAlgHom e f.hom.hom)
  map_id := sorry
  map_comp := sorry

/-- Reindexing sends an algebra to the same carrier with transported scalars. -/
theorem reindex_obj {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (C : IndEtale.{u} R) :
    ((reindex e).obj C).obj = @CommAlgCat.of S _ C _ (algebraCompRingEquiv e C) :=
  sorry

end CommAlgCat.IndEtale

namespace AlgebraicGeometry.Scheme.ProEt

/-- Global sections of an affine ind-étale object are an algebra over the base. -/
instance AffineIndEtale.instAlgebra (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) : Algebra Γ(S, ⊤) Γ(U.obj.left, ⊤) :=
  (U.obj.hom.appTop).hom.toAlgebra

/-- The structure map of `AffineIndEtale.instAlgebra` is the map on global sections. -/
theorem AffineIndEtale.algebraMap_eq (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    algebraMap Γ(S, ⊤) Γ(U.obj.left, ⊤) = (U.obj.hom.appTop).hom := sorry

/-- The spectrum of an ind-étale `Γ(S, ⊤)`-algebra, as a scheme over `S`. -/
def AffineIndEtale.specHom (S : Scheme.{u}) [IsAffine S]
    (C : CommAlgCat.IndEtale.{u} Γ(S, ⊤)) :
    Spec (CommRingCat.of (C : Type u)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)) ≫ S.isoSpec.inv

/-- Unfolding lemma for `AffineIndEtale.specHom`. -/
theorem AffineIndEtale.specHom_def (S : Scheme.{u}) [IsAffine S]
    (C : CommAlgCat.IndEtale.{u} Γ(S, ⊤)) :
    specHom S C =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)) ≫ S.isoSpec.inv :=
  sorry

/-- Spectra of ind-étale algebras are weakly étale over an affine base. -/
instance AffineIndEtale.specHom_weaklyEtale (S : Scheme.{u}) [IsAffine S]
    (C : CommAlgCat.IndEtale.{u} Γ(S, ⊤)) :
    WeaklyEtale (specHom S C) := sorry

/-- The map on global sections of `specHom` is ind-étale. -/
theorem AffineIndEtale.specHom_appTop_indEtale (S : Scheme.{u}) [IsAffine S]
    (C : CommAlgCat.IndEtale.{u} Γ(S, ⊤)) :
    ((specHom S C).appTop).hom.IndEtale := sorry

/-- The commuting witness for `ofIndEtale` on morphisms of ind-étale algebras. -/
theorem AffineIndEtale.ofIndEtale_map_w (S : Scheme.{u}) [IsAffine S]
    {C D : (CommAlgCat.IndEtale.{u} Γ(S, ⊤))ᵒᵖ} (f : C ⟶ D) :
    Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) ≫ specHom S D.unop =
      specHom S C.unop := sorry

/-- Global sections as a functor from affine ind-étale objects to opposite
ind-étale algebras. -/
def AffineIndEtale.toIndEtale (S : Scheme.{u}) [IsAffine S] :
    AffineIndEtale S ⥤ (CommAlgCat.IndEtale.{u} Γ(S, ⊤))ᵒᵖ where
  obj U :=
    op (CommAlgCat.IndEtale.of Γ(S, ⊤) Γ(U.obj.left, ⊤) U.property.2)
  map {U V} f :=
    (CommAlgCat.IndEtale.ofHom V.property.2 U.property.2
      { (f.hom.left.appTop).hom with commutes' := sorry }).op
  map_id := sorry
  map_comp := sorry

/-- The underlying algebra of `toIndEtale` is the ring of global sections. -/
theorem AffineIndEtale.toIndEtale_obj (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    ((toIndEtale S).obj U).unop =
      CommAlgCat.IndEtale.of Γ(S, ⊤) Γ(U.obj.left, ⊤) U.property.2 := sorry

/-- Spectra of ind-étale algebras as a functor to affine ind-étale objects. -/
def AffineIndEtale.ofIndEtale (S : Scheme.{u}) [IsAffine S] :
    (CommAlgCat.IndEtale.{u} Γ(S, ⊤))ᵒᵖ ⥤ AffineIndEtale S where
  obj C := AffineIndEtale.mk (specHom S C.unop) (specHom_appTop_indEtale S C.unop)
  map {C D} f :=
    homMk (MorphismProperty.Over.homMk
      (Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom))
      (ofIndEtale_map_w S f))
  map_id := sorry
  map_comp := sorry

/-- The underlying scheme of `ofIndEtale` is the spectrum of the algebra. -/
theorem AffineIndEtale.ofIndEtale_obj (S : Scheme.{u}) [IsAffine S]
    (C : (CommAlgCat.IndEtale.{u} Γ(S, ⊤))ᵒᵖ) :
    ((ofIndEtale S).obj C).obj.left = Spec (CommRingCat.of (C.unop : Type u)) :=
  sorry

/-- `ofIndEtaleCounitApp` commutes with the structure maps to `S`. -/
theorem AffineIndEtale.ofIndEtaleCounitApp_w (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    U.obj.left.isoSpec.inv ≫ U.obj.hom =
      specHom S ((toIndEtale S).obj U).unop := sorry

/-- The comparison from the spectrum of global sections back to an affine
ind-étale object. -/
def AffineIndEtale.ofIndEtaleCounitApp (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    (ofIndEtale S).obj ((toIndEtale S).obj U) ⟶ U :=
  homMk (MorphismProperty.Over.homMk U.obj.left.isoSpec.inv
    (ofIndEtaleCounitApp_w S U))

/-- The underlying scheme morphism of `ofIndEtaleCounitApp` is `isoSpec.inv`. -/
theorem AffineIndEtale.ofIndEtaleCounitApp_left (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    (ofIndEtaleCounitApp S U).hom.left = U.obj.left.isoSpec.inv := sorry

/-- The kernel of the map on global sections induced by a closed immersion of
affine schemes. -/
def AffineIndEtale.ker {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]
    (i : Z ⟶ X) [IsClosedImmersion i] : Ideal Γ(X, ⊤) :=
  RingHom.ker i.appTop.hom

/-- Unfolding lemma for `AffineIndEtale.ker`. -/
theorem AffineIndEtale.ker_eq {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ker i = RingHom.ker i.appTop.hom := sorry

/-- A closed immersion of affines identifies `Γ(Z, ⊤)` with `Γ(X, ⊤) ⧸ ker i`. -/
def AffineIndEtale.quotientIso {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (Γ(X, ⊤) ⧸ ker i) ≃+* Γ(Z, ⊤) :=
  RingHom.quotientKerEquivOfSurjective
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2

/-- The quotient comparison sends the class of a global section to its image
in `Γ(Z, ⊤)`. -/
theorem AffineIndEtale.quotientIso_apply_mk {X Z : Scheme.{u}} [IsAffine X]
    [IsAffine Z] (i : Z ⟶ X) [IsClosedImmersion i] (a : Γ(X, ⊤)) :
    quotientIso i (Ideal.Quotient.mk (ker i) a) = i.appTop.hom a := sorry

end AlgebraicGeometry.Scheme.ProEt
