module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtale
public import ReasLib.Algebra.Category.CommAlgCat.IndEtale.Objects

/-!
# Spectra and global sections of affine ind-étale objects
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty Opposite AlgebraicGeometry CommAlgCat
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Global sections of an affine ind-étale object are an algebra over the base. -/
instance AffineIndEtale.instAlgebra (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) : Algebra Γ(S, ⊤) Γ(U.obj.left, ⊤) :=
  (U.obj.hom.appTop).hom.toAlgebra

/-- The structure map of `AffineIndEtale.instAlgebra` is the map on global sections. -/
theorem AffineIndEtale.algebraMap_eq (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    algebraMap Γ(S, ⊤) Γ(U.obj.left, ⊤) = (U.obj.hom.appTop).hom := rfl

/-- The spectrum of an ind-étale `Γ(S, ⊤)`-algebra, as a scheme over `S`. -/
def AffineIndEtale.specHom (S : Scheme.{u}) [IsAffine S]
    (C : CommAlgCat.IndEtale.{u} Γ(S, ⊤)) :
    Spec (CommRingCat.of (C : Type u)) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) C)) ≫ S.isoSpec.inv

/-- Spectra of ind-étale algebras are weakly étale over an affine base. -/
instance AffineIndEtale.specHom_weaklyEtale (S : Scheme.{u}) [IsAffine S]
    (C : CommAlgCat.IndEtale.{u} Γ(S, ⊤)) :
    WeaklyEtale (specHom S C) := sorry

/-- The map on global sections of `specHom` is ind-étale. -/
theorem AffineIndEtale.specHom_appTop_indEtale (S : Scheme.{u}) [IsAffine S]
    (C : CommAlgCat.IndEtale.{u} Γ(S, ⊤)) :
    ((specHom S C).appTop).hom.IndEtale := sorry

/-- Spectrum maps of algebra homomorphisms commute with the maps to the base. -/
private theorem AffineIndEtale.ofIndEtale_map_w (S : Scheme.{u}) [IsAffine S]
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
  map_id := by
    intro U
    apply Quiver.Hom.unop_inj
    ext x
    change (CommRingCat.Hom.hom (Scheme.Hom.appTop (𝟙 U.obj.left))) x = x
    rfl
  map_comp := by
    intro U V W f g
    apply Quiver.Hom.unop_inj
    ext x
    change (CommRingCat.Hom.hom ((f.hom.left ≫ g.hom.left).appTop)) x = _
    simp

/-- The underlying algebra of `toIndEtale` is the ring of global sections. -/
theorem AffineIndEtale.toIndEtale_obj (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    ((toIndEtale S).obj U).unop =
      CommAlgCat.IndEtale.of Γ(S, ⊤) Γ(U.obj.left, ⊤) U.property.2 := rfl

/-- Spectra of ind-étale algebras as a functor to affine ind-étale objects. -/
def AffineIndEtale.ofIndEtale (S : Scheme.{u}) [IsAffine S] :
    (CommAlgCat.IndEtale.{u} Γ(S, ⊤))ᵒᵖ ⥤ AffineIndEtale S where
  obj C := AffineIndEtale.mk (specHom S C.unop) (specHom_appTop_indEtale S C.unop)
  map {C D} f :=
    homMk (MorphismProperty.Over.homMk
      (Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom))
      (by exact AffineIndEtale.ofIndEtale_map_w S f))
  map_id := by
    intro U
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_id _
  map_comp := by
    intro U V W f g
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    change Spec.map
      (CommRingCat.ofHom g.unop.hom.hom.toRingHom ≫
        CommRingCat.ofHom f.unop.hom.hom.toRingHom) = _
    exact Spec.map_comp _ _

/-- The underlying scheme of `ofIndEtale` is the spectrum of the algebra. -/
theorem AffineIndEtale.ofIndEtale_obj (S : Scheme.{u}) [IsAffine S]
    (C : (CommAlgCat.IndEtale.{u} Γ(S, ⊤))ᵒᵖ) :
    ((ofIndEtale S).obj C).obj.left = Spec (CommRingCat.of (C.unop : Type u)) :=
  rfl

/-- The affine spectrum comparison commutes with the structure map to the base. -/
private theorem AffineIndEtale.ofIndEtaleCounitApp_w (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    U.obj.left.isoSpec.inv ≫ U.obj.hom =
      specHom S ((toIndEtale S).obj U).unop := sorry


/-- The comparison from the spectrum of global sections back to an affine
ind-étale object. -/
def AffineIndEtale.ofIndEtaleCounitApp (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    (ofIndEtale S).obj ((toIndEtale S).obj U) ⟶ U :=
  homMk (MorphismProperty.Over.homMk U.obj.left.isoSpec.inv
    (by exact AffineIndEtale.ofIndEtaleCounitApp_w S U))

/-- The underlying scheme morphism of `ofIndEtaleCounitApp` is `isoSpec.inv`. -/
theorem AffineIndEtale.ofIndEtaleCounitApp_left (S : Scheme.{u}) [IsAffine S]
    (U : AffineIndEtale S) :
    (ofIndEtaleCounitApp S U).hom.left = U.obj.left.isoSpec.inv := rfl

/-- Global sections are fully faithful on affine ind-étale objects, with preimages
obtained by conjugating spectrum maps by the affine comparison isomorphisms. -/
def AffineIndEtale.toIndEtaleFullyFaithful (S : Scheme.{u}) [IsAffine S] :
    (AffineIndEtale.toIndEtale S).FullyFaithful where
  preimage {U V} f :=
    homMk (MorphismProperty.Over.homMk
      (U.obj.left.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) ≫ V.obj.left.isoSpec.inv)
      (by sorry))
  map_preimage := sorry
  preimage_map := sorry

/-- Conjugating global sections by the canonical spectrum comparisons preserves scalars. -/
private theorem AffineIndEtale.ofIndEtalePreimage_commutes (S : Scheme.{u}) [IsAffine S]
    {C D : (CommAlgCat.IndEtale.{u} Γ(S, ⊤))ᵒᵖ}
    (f : (ofIndEtale S).obj C ⟶ (ofIndEtale S).obj D) (r : Γ(S, ⊤)) :
    (((Scheme.ΓSpecIso (CommRingCat.of (D.unop : Type u))).inv ≫
        f.hom.left.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (C.unop : Type u))).hom).hom)
      (algebraMap Γ(S, ⊤) D.unop r) = algebraMap Γ(S, ⊤) C.unop r := sorry

/-- Global sections conjugated by the canonical spectrum comparisons give a morphism
of opposite ind-étale algebras. -/
private def AffineIndEtale.ofIndEtalePreimage (S : Scheme.{u}) [IsAffine S]
    {C D : (CommAlgCat.IndEtale.{u} Γ(S, ⊤))ᵒᵖ}
    (f : (ofIndEtale S).obj C ⟶ (ofIndEtale S).obj D) : C ⟶ D :=
  (CommAlgCat.IndEtale.ofHom D.unop.property C.unop.property
    { ((Scheme.ΓSpecIso (CommRingCat.of (D.unop : Type u))).inv ≫
        f.hom.left.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (C.unop : Type u))).hom).hom with
      commutes' := ofIndEtalePreimage_commutes S f }).op

/-- Taking spectra of the conjugated global-sections morphism recovers the original morphism. -/
private theorem AffineIndEtale.ofIndEtale_map_preimage (S : Scheme.{u}) [IsAffine S]
    {C D : (CommAlgCat.IndEtale.{u} Γ(S, ⊤))ᵒᵖ}
    (f : (ofIndEtale S).obj C ⟶ (ofIndEtale S).obj D) :
    (ofIndEtale S).map (ofIndEtalePreimage S f) = f := sorry

/-- Conjugated global sections of a spectrum morphism recover the opposite algebra morphism. -/
private theorem AffineIndEtale.ofIndEtale_preimage_map (S : Scheme.{u}) [IsAffine S]
    {C D : (CommAlgCat.IndEtale.{u} Γ(S, ⊤))ᵒᵖ} (f : C ⟶ D) :
    ofIndEtalePreimage S ((ofIndEtale S).map f) = f := sorry

end AlgebraicGeometry.Scheme.ProEt

end

end

public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Spectra are fully faithful on opposite ind-étale algebras, with preimages
given by global sections and the canonical global-sections comparison. -/
def AffineIndEtale.ofIndEtaleFullyFaithful (S : Scheme.{u}) [IsAffine S] :
    (AffineIndEtale.ofIndEtale S).FullyFaithful where
  preimage := by exact AffineIndEtale.ofIndEtalePreimage S
  map_preimage := by exact AffineIndEtale.ofIndEtale_map_preimage S
  preimage_map := by exact AffineIndEtale.ofIndEtale_preimage_map S

end AlgebraicGeometry.Scheme.ProEt
