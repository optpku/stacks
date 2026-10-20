module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Instances

/-! # Coimages of residue-identified Artinian local algebras -/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {A B : ArtinianLocalAlgCat Λ k}

/-- Morphisms of residue-identified Artinian local algebras are equal when their
underlying algebra maps are equal. -/
theorem hom_ext {A B : ArtinianLocalAlgCat Λ k} {f g : A ⟶ B} (h : f.hom = g.hom) : f = g := by
  rcases f with ⟨f, hf, hfc⟩
  rcases g with ⟨g, hg, hgc⟩
  change f = g at h
  subst g
  rfl

/-- The kernel of a morphism of `ArtinianLocalAlgCat` is contained in the maximal ideal. -/
theorem ker_le_maximalIdeal (f : A ⟶ B) :
    RingHom.ker f.hom.toRingHom ≤ maximalIdeal A.carrier :=
  (Ideal.ker_le_comap f.hom.toRingHom (K := maximalIdeal B.carrier)).trans
    (le_of_eq
      (@maximalIdeal_comap A.carrier B.carrier _ _ _ _ f.hom.toRingHom
        (isLocalHom_toRingHom f.hom)))

/-- The coimage carrier of a morphism of local algebras is nontrivial. -/
instance instNontrivial_kerQuotient (f : A ⟶ B) :
    Nontrivial (A.carrier ⧸ RingHom.ker f.hom.toRingHom) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (mt (fun h => top_le_iff.mp (Eq.trans_le (Eq.symm h) (ker_le_maximalIdeal f)))
      (Ideal.IsMaximal.ne_top (maximalIdeal.isMaximal A.carrier)))

/-- The coimage carrier of a morphism of local algebras is local. -/
instance instIsLocalRing_kerQuotient (f : A ⟶ B) :
    IsLocalRing (A.carrier ⧸ RingHom.ker f.hom.toRingHom) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- Residue identification of the coimage of `f` with `k`, via the third isomorphism
theorem and the residue identification of the domain. -/
noncomputable def imageResidueFieldIso (f : A ⟶ B) :
    ResidueField (A.carrier ⧸ RingHom.ker f.hom.toRingHom) ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
      (map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk (RingHom.ker f.hom.toRingHom))
        Ideal.Quotient.mk_surjective).symm).trans
    ((DoubleQuot.quotQuotEquivQuotOfLEₐ Λ (ker_le_maximalIdeal f)).trans A.residueFieldIso)

/-- The coimage `A ⧸ ker f` of a morphism of residue-identified Artinian local algebras. -/
noncomputable def image (f : A ⟶ B) : ArtinianLocalAlgCat Λ k :=
  of (A.carrier ⧸ RingHom.ker f.hom.toRingHom) (imageResidueFieldIso f)

/-- The carrier of `image f` is the quotient of the domain by `ker f`. -/
theorem image_carrier (f : A ⟶ B) :
    (image f).carrier = (A.carrier ⧸ RingHom.ker f.hom.toRingHom) := sorry

/-- The quotient algebra map from an algebra to its coimage. -/
noncomputable def toImageHom (f : A ⟶ B) : algebraHom A (image f) :=
  Ideal.Quotient.mkₐ Λ (RingHom.ker f.hom.toRingHom)

/-- The quotient projection onto the coimage is local. -/
theorem toImage_isLocalHom (f : A ⟶ B) : IsLocalHom (toImageHom f) := sorry

/-- The quotient projection preserves the chosen residue identification. -/
theorem toImage_residue_compat (f : A ⟶ B) :
    residueCompat (toImageHom f) (toImage_isLocalHom f) = residueIsoHom A := sorry

/-- The canonical surjection from the domain of a morphism onto its coimage. -/
noncomputable def toImage (f : A ⟶ B) : A ⟶ image f :=
  Hom.of (toImageHom f) (toImage_isLocalHom f) (toImage_residue_compat f)

/-- The algebra map from the quotient by the kernel to the codomain. -/
noncomputable def imageιHom (f : A ⟶ B) : algebraHom (image f) B :=
  Ideal.Quotient.liftₐ (RingHom.ker f.hom.toRingHom) f.hom
    (fun _ ha => RingHom.mem_ker.mp ha)

/-- The algebra map from a coimage into the codomain is local. -/
theorem imageι_isLocalHom (f : A ⟶ B) : IsLocalHom (imageιHom f) := sorry

/-- The inclusion of a coimage preserves the chosen residue identification. -/
theorem imageι_residue_compat (f : A ⟶ B) :
    residueCompat (imageιHom f) (imageι_isLocalHom f) = residueIsoHom (image f) := sorry

/-- The canonical injection of the coimage into the codomain. -/
noncomputable def imageι (f : A ⟶ B) : image f ⟶ B :=
  Hom.of (imageιHom f) (imageι_isLocalHom f) (imageι_residue_compat f)

/-- The coimage factorization identity `toImage f ≫ imageι f = f`. -/
theorem image_fac (f : A ⟶ B) : toImage f ≫ imageι f = f :=
  hom_ext
    (Ideal.Quotient.liftₐ_comp (RingHom.ker f.hom.toRingHom) f.hom
      (fun _ ha => RingHom.mem_ker.mp ha))

/-- The coimage projection `toImage f` is surjective. -/
theorem toImage_surjective (f : A ⟶ B) : Function.Surjective (toImage f).hom := sorry

/-- The coimage inclusion `imageι f` is injective. -/
theorem imageι_injective (f : A ⟶ B) : Function.Injective (imageι f).hom := sorry

/-- Commutative squares of `ArtinianLocalAlgCat` induce maps of kernels. -/
theorem imageMap_le {A₁ B₁ A₂ B₂ : ArtinianLocalAlgCat Λ k}
    (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂) (α : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (h : f ≫ β = α ≫ g) :
    RingHom.ker f.hom.toRingHom ≤ (RingHom.ker g.hom.toRingHom).comap α.hom.toRingHom :=
  fun x hx =>
    Ideal.mem_comap.mpr
      (RingHom.mem_ker.mpr
        ((AlgHom.comp_apply g.hom α.hom x).symm.trans
          ((AlgHom.congr_fun (congrArg Hom.hom h.symm) x).trans
            ((AlgHom.comp_apply β.hom f.hom x).trans
              ((congrArg (fun y => β.hom y) (RingHom.mem_ker.mp hx)).trans
                (map_zero β.hom))))))

/-- A commutative square induces an algebra map between the quotients by its kernels. -/
noncomputable def imageMapHom {A₁ B₁ A₂ B₂ : ArtinianLocalAlgCat Λ k}
    (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂) (α : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (h : f ≫ β = α ≫ g) :
    algebraHom (image f) (image g) :=
  Ideal.quotientMapₐ (RingHom.ker g.hom.toRingHom) α.hom (imageMap_le f g α β h)

/-- The map of coimages induced by a commutative square is local. -/
theorem imageMap_isLocalHom {A₁ B₁ A₂ B₂ : ArtinianLocalAlgCat Λ k}
    (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂) (α : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (h : f ≫ β = α ≫ g) :
    IsLocalHom (imageMapHom f g α β h) := sorry

/-- The map of coimages induced by a commutative square preserves residue identifications. -/
theorem imageMap_residue_compat {A₁ B₁ A₂ B₂ : ArtinianLocalAlgCat Λ k}
    (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂) (α : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (h : f ≫ β = α ≫ g) :
    residueCompat (imageMapHom f g α β h) (imageMap_isLocalHom f g α β h) =
      residueIsoHom (image f) := sorry

/-- The coimage map induced by a commutative square of Artinian local algebras. -/
noncomputable def imageMap {A₁ B₁ A₂ B₂ : ArtinianLocalAlgCat Λ k}
    (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂) (α : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (h : f ≫ β = α ≫ g) :
    image f ⟶ image g :=
  Hom.of (imageMapHom f g α β h) (imageMap_isLocalHom f g α β h)
    (imageMap_residue_compat f g α β h)

end ArtinianLocalAlgCat
