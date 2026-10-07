module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeProjFromSections.OnSource

/-!
# Characterizations of relative ampleness

Relative ampleness can be tested on open covers of the base and characterized by the morphism
from the source to a relative projective spectrum induced by a multiplicative system of sections.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section


variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)

/-- A module is relatively ample on an open cover of the base when each restriction to the
corresponding base-open preimage is relatively ample. -/
def RelativelyAmpleOnBaseOpenCover : Prop :=
  ∃ (ι : Type u) (V : ι → S.Opens), TopologicalSpace.IsOpenCover V ∧
    ∀ i : ι, RelativelyAmple (f ∣_ V i) (restrictToBasePreimage f L (V i))

/-- A module is ample on an affine open cover of the base when every cover member is affine and
the restriction to its preimage is an ample invertible module. -/
def AmpleOnAffineBaseOpenCover : Prop :=
  ∃ (ι : Type u) (V : ι → S.Opens), TopologicalSpace.IsOpenCover V ∧
    (∀ i : ι, IsAffineOpen (V i)) ∧
      ∀ i : ι, IsAmpleOnBasePreimage f L (V i)

/-- A commutative graded algebra sheaf supports a canonical full-source relative projective
section map with a prescribed morphism property and a prescribed condition on its multiplicative
section homomorphism. -/
def HasRelativeProjSectionMapWith
    [hL : Scheme.Modules.Invertible L]
    (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) [hcomm : 𝒜.IsCommutative]
    (Q : MorphismProperty Scheme.{u})
    (extra : Scheme.RelativeProjTwist.Hom 𝒜 f
      (@RingedSpace.InvertiblePower.gradedAlgebra _ L
        (Scheme.Modules.Invertible.ringedSpaceIsInvertible hL)) → Prop) : Prop :=
  let conditionForFunctor := fun
      (hqc : 𝒜.IsQuasicoherent)
      (A σ : S.affineOpens → Type u)
      [hA : ∀ U, CommRing (A U)] [hσ : ∀ U, SetLike (σ U) (A U)]
      [hadd : ∀ U, AddSubgroupClass (σ U) (A U)]
      (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
      [hgraded : ∀ U, GradedRing (sectionGrading U)]
      (model : ∀ (U : S.affineOpens) (d : ℕ),
        (𝒜 (Int.ofNat d)).val.obj (op (U : S.Opens)) ≃+ sectionGrading U d)
      (hModel : ∀ U : S.affineOpens,
        AffineOpenSectionProj.IsAffineOpenSectionModel (sectionGrading U) 𝒜 U (model U))
      (twistPresentation : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
      (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
        (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
      (sectionRestrict_spec :
        ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
          (d : ℕ) (x : sectionGrading U' d),
          model U d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom) ((model U' d).symm x)) =
            (sectionRestrict h).gradedAddHom d x)
      (R : Scheme.RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel
        twistPresentation sectionRestrict sectionRestrict_spec)
      (presentation : Scheme.RelativeProjTwist.Presentation 𝒜 A σ sectionGrading
        twistPresentation (fun U d ↦ (model U d).toEquiv) (Scheme.relativeProjπ R))
      (ψ : Scheme.RelativeProjTwist.Hom 𝒜 f
        (@RingedSpace.InvertiblePower.gradedAlgebra _ L
          (Scheme.Modules.Invertible.ringedSpaceIsInvertible hL)))
      [F : RelativeProjFunctor S 𝒜] =>
    ∃ (associatedToQuadruples : ∀ d : {n : ℕ // 1 ≤ n},
        (F.degreeFunctor d).IsAssociatedToQuadruples)
      (representedPoint : F.toFunctor.obj (op (Scheme.relativeProj R)))
      (c : Scheme.Modules.RelativeProjSectionMap 𝒜 hqc A σ sectionGrading model hModel
        twistPresentation sectionRestrict sectionRestrict_spec R presentation f L ψ),
      Scheme.Modules.RelativeProjSectionMap.IsCanonical
          (𝒜 := 𝒜)
          (associatedToQuadruples := associatedToQuadruples)
          (representedPoint := representedPoint) (c := c) ∧
        ∃ hTop : c.domain = ⊤,
          Q (Scheme.Modules.RelativeProjSectionMap.mapOnSource
            𝒜 hqc A σ sectionGrading model hModel twistPresentation sectionRestrict
            sectionRestrict_spec R presentation f L ψ c hTop)
  let conditionForGrading := fun
      (hqc : 𝒜.IsQuasicoherent)
      (A σ : S.affineOpens → Type u)
      [hA : ∀ U, CommRing (A U)] [hσ : ∀ U, SetLike (σ U) (A U)]
      [hadd : ∀ U, AddSubgroupClass (σ U) (A U)]
      (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
      [hgraded : ∀ U, GradedRing (sectionGrading U)] =>
    ∃ (model : ∀ (U : S.affineOpens) (d : ℕ),
        (𝒜 (Int.ofNat d)).val.obj (op (U : S.Opens)) ≃+ sectionGrading U d)
      (hModel : ∀ U : S.affineOpens,
        AffineOpenSectionProj.IsAffineOpenSectionModel (sectionGrading U) 𝒜 U (model U))
      (twistPresentation : ∀ U : S.affineOpens, ProjTwistPresentation (sectionGrading U))
      (sectionRestrict : ∀ ⦃U U' : S.affineOpens⦄,
        (U : S.Opens) ≤ (U' : S.Opens) → sectionGrading U' →+*ᵍ sectionGrading U)
      (sectionRestrict_spec :
        ∀ ⦃U U' : S.affineOpens⦄ (h : (U : S.Opens) ≤ (U' : S.Opens))
          (d : ℕ) (x : sectionGrading U' d),
          model U d
              ((((𝒜 (Int.ofNat d)).val.map (homOfLE h).op).hom) ((model U' d).symm x)) =
            (sectionRestrict h).gradedAddHom d x)
      (R : Scheme.RelativeProjRealization 𝒜 hqc A σ sectionGrading model hModel
        twistPresentation sectionRestrict sectionRestrict_spec)
      (presentation : Scheme.RelativeProjTwist.Presentation 𝒜 A σ sectionGrading
        twistPresentation (fun U d ↦ (model U d).toEquiv) (Scheme.relativeProjπ R))
      (ψ : Scheme.RelativeProjTwist.Hom 𝒜 f
        (@RingedSpace.InvertiblePower.gradedAlgebra _ L
          (Scheme.Modules.Invertible.ringedSpaceIsInvertible hL))),
      extra ψ ∧
        ∃ F : RelativeProjFunctor S 𝒜,
          conditionForFunctor hqc A σ sectionGrading model hModel twistPresentation
            sectionRestrict sectionRestrict_spec R presentation ψ (F := F)
  let conditionForSubgroups := fun
      (hqc : 𝒜.IsQuasicoherent)
      (A σ : S.affineOpens → Type u)
      [hA : ∀ U, CommRing (A U)] [hσ : ∀ U, SetLike (σ U) (A U)]
      [hadd : ∀ U, AddSubgroupClass (σ U) (A U)] =>
    ∃ (sectionGrading : ∀ U : S.affineOpens, ℕ → σ U)
      (hgraded : ∀ U, GradedRing (sectionGrading U)),
      conditionForGrading hqc A σ sectionGrading (hgraded := hgraded)
  let conditionForSetLike := fun
      (hqc : 𝒜.IsQuasicoherent)
      (A σ : S.affineOpens → Type u)
      [hA : ∀ U, CommRing (A U)] [hσ : ∀ U, SetLike (σ U) (A U)] =>
    ∃ hadd : ∀ U, AddSubgroupClass (σ U) (A U),
      conditionForSubgroups hqc A σ (hadd := hadd)
  let conditionForRings := fun
      (hqc : 𝒜.IsQuasicoherent)
      (A : S.affineOpens → Type u) [hA : ∀ U, CommRing (A U)] =>
    ∃ (σ : S.affineOpens → Type u) (hσ : ∀ U, SetLike (σ U) (A U)),
      conditionForSetLike hqc A σ (hσ := hσ)
  ∃ (hqc : 𝒜.IsQuasicoherent) (A : S.affineOpens → Type u)
    (hA : ∀ U, CommRing (A U)),
    conditionForRings hqc A (hA := hA)

/-- There is a full-domain canonical relative projective section map induced by a multiplicative
system of sections and having the specified morphism property. -/
def HasRelativeProjSectionMap [hL : Scheme.Modules.Invertible L]
    (Q : MorphismProperty Scheme.{u}) : Prop :=
  ∃ (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) (hcomm : 𝒜.IsCommutative),
    HasRelativeProjSectionMapWith f L 𝒜 Q (fun _ ↦ True)
      (hL := hL) (hcomm := hcomm)

/-- The canonical pushforward algebra of the nonnegative tensor powers admits a full-domain
canonical relative projective section map that is an open immersion. -/
def HasCanonicalOpenImmersionRelativeProjSectionMap
    [hL : Scheme.Modules.Invertible L] : Prop :=
  QuasiSeparated f ∧
    ∃ (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) (hcomm : 𝒜.IsCommutative),
      HasRelativeProjSectionMapWith f L 𝒜 @IsOpenImmersion
        (fun ψ ↦
          ∃ hcanonical : ∀ d : ℕ,
              𝒜 (Int.ofNat d) =
                (Scheme.Modules.pushforward f).obj (RingedSpace.TensorPower.sheaf L d),
            ∀ d : ℕ,
              ψ.hom d = eqToHom (hcanonical d) ≫
                (Scheme.Modules.pushforward f).map
                  (@RingedSpace.InvertiblePower.natIso _ L
                    (Scheme.Modules.Invertible.ringedSpaceIsInvertible hL) d).hom)
        (hL := hL) (hcomm := hcomm)

/-- For a quasi-compact morphism and an invertible module, relative ampleness, its open-local and
affine-local forms, and the open-immersion, canonical open-immersion, and immersion relative
projective section-map criteria are equivalent. -/
@[stacks 01VJ]
theorem relativelyAmple_tfae
    [QuasiCompact f] [Scheme.Modules.Invertible L] :
    List.TFAE [
      RelativelyAmple f L,
      RelativelyAmpleOnBaseOpenCover f L,
      AmpleOnAffineBaseOpenCover f L,
      HasRelativeProjSectionMap f L @IsOpenImmersion,
      HasCanonicalOpenImmersionRelativeProjSectionMap f L,
      HasRelativeProjSectionMap f L @IsImmersion] := sorry

/-- Over an affine base, an invertible module is relatively ample precisely when it is ample on
the source scheme. -/
theorem relativelyAmple_iff_isAmple_of_isAffine
    [IsAffine S] [Scheme.Modules.Invertible L] :
    RelativelyAmple f L ↔ Scheme.Modules.IsAmple L := sorry

/-- On an affine base, an ample invertible module is canonically relatively ample. -/
instance instRelativelyAmpleOfIsAmpleOfIsAffine
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) [IsAffine S]
    [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L] :
    RelativelyAmple f L := sorry

end


end AlgebraicGeometry
