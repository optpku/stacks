/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.FromSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GradedSections.Grading
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.InvertiblePower
public import ReasLib.AlgebraicGeometry.Scheme.Module.SectionRingProj

/-!
# Morphisms to projective spectra from sections of an invertible module

A graded homomorphism into the tensor-power section ring determines a canonical open domain and
a canonical projective-spectrum morphism together with its comparison of integral twists.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {T : Scheme.{u}} (L : T.Modules) [Invertible L]

/-- The tensor-power section represented by the image of a homogeneous element under a graded
ring homomorphism. -/
noncomputable def projSectionMapDegreeSection
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (d : ℕ) (x : 𝒜 d) : Γ(RingedSpace.TensorPower.sheaf L d, ⊤) :=
  (DirectSum.InternalGrading.summandEquiv
    (RingedSpace.GradedSections.degree L) d).symm (ψ.gradedAddHom d x)

/-- The natural domain of a graded section map is the union of the nonvanishing opens of all
positive homogeneous images. -/
noncomputable def projSectionMapDomain
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L) : T.Opens :=
  ⨆ f : PositiveHomogeneous 𝒜,
    (inferInstance : Invertible L).nonvanishingOpen
      (projSectionMapDegreeSection 𝒜 L ψ f.degree
        ⟨f.1, PositiveHomogeneous.mem_degree f⟩)

/-- A projective-spectrum map from the natural section-map domain, together with a morphism from
the pulled-back integral twist algebra to the pulled-back integral powers of the invertible
module. -/
structure ProjSectionMap
    (P : ProjTwistPresentation 𝒜)
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L) where
  /-- The morphism from the natural domain to the projective spectrum. -/
  map : (projSectionMapDomain 𝒜 L ψ).toScheme ⟶ Proj 𝒜
  /-- The comparison as a morphism of integral graded algebra sheaves. -/
  theta : P.twistAlgebra.pullbackAlgebra map ⟶
    pullbackInvertiblePowerGradedAlgebra (projSectionMapDomain 𝒜 L ψ).ι L

namespace ProjSectionMap

variable {𝒜 L}
variable {P : ProjTwistPresentation 𝒜}
variable {ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L}

/-- Construct a projective section map from its morphism and its graded-algebra comparison. -/
def of
    (map : (projSectionMapDomain 𝒜 L ψ).toScheme ⟶ Proj 𝒜)
    (theta : P.twistAlgebra.pullbackAlgebra map ⟶
      pullbackInvertiblePowerGradedAlgebra (projSectionMapDomain 𝒜 L ψ).ι L) :
    ProjSectionMap 𝒜 L P ψ where
  map := map
  theta := theta

/-- The degree-`n` component of the comparison on the actual pulled-back twist. -/
def component (c : ProjSectionMap 𝒜 L P ψ) (n : ℤ) :
    (Scheme.Modules.pullback c.map).obj (P.actualTwist n) ⟶
      pullbackInvertiblePower (projSectionMapDomain 𝒜 L ψ).ι L n :=
  (P.twistAlgebra.pullbackIso c.map n).hom ≫ c.theta.hom n

/-- The degree-zero comparison preserves the canonical unit section. -/
theorem component_map_one (c : ProjSectionMap 𝒜 L P ψ)
    (U : ((projSectionMapDomain 𝒜 L ψ).toScheme.Opens)ᵒᵖ) :
    (((c.component 0).val.app U).hom) (P.actualOne c.map U) =
      pullbackInvertiblePowerOne (projSectionMapDomain 𝒜 L ψ).ι L U := sorry

/-- The comparison preserves multiplication of homogeneous local sections. -/
theorem component_map_mul (c : ProjSectionMap 𝒜 L P ψ)
    (U : ((projSectionMapDomain 𝒜 L ψ).toScheme.Opens)ᵒᵖ)
    (a b : ℤ) (x : projTwistPullbackSection P.actualTwist c.map a U)
    (y : projTwistPullbackSection P.actualTwist c.map b U) :
    (((c.component (a + b)).val.app U).hom) (P.actualMul c.map U a b x y) =
      pullbackInvertiblePowerMul (projSectionMapDomain 𝒜 L ψ).ι L U a b
        ((((c.component a).val.app U).hom) x)
        ((((c.component b).val.app U).hom) y) := sorry

/-- A projective section map is canonical when it has the prescribed inverse images of positive
homogeneous basic opens and induces the prescribed map on every nonnegative homogeneous
section. -/
def IsCanonical (c : ProjSectionMap 𝒜 L P ψ) : Prop :=
  (∀ {f : A} {d : ℕ} (_ : 0 < d) (hf : f ∈ 𝒜 d),
    (projSectionMapDomain 𝒜 L ψ).ι ''ᵁ (c.map ⁻¹ᵁ Proj.basicOpen 𝒜 f) =
      (inferInstance : Invertible L).nonvanishingOpen
        (projSectionMapDegreeSection 𝒜 L ψ d ⟨f, hf⟩)) ∧
  ∀ d : ℕ, ∀ x : 𝒜 d,
    ((P.actualSectionMap d ≫
        globalSectionsPullback c.map (P.actualTwist (d : ℤ)) ≫
        globalSectionsMap (c.component (d : ℤ))).hom) x =
      ((globalSectionsMap
          (@RingedSpace.InvertiblePower.natIso _ L
            (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L)) d).hom ≫
        globalSectionsPullback (projSectionMapDomain 𝒜 L ψ).ι
          (tensorPowerInt L (d : ℤ))).hom)
        (projSectionMapDegreeSection 𝒜 L ψ d x)

namespace IsCanonical

/-- The inverse image of a positive homogeneous basic open is its section nonvanishing open. -/
theorem preimage_basicOpen {c : ProjSectionMap 𝒜 L P ψ} (hc : c.IsCanonical)
    {f : A} {d : ℕ} (hd : 0 < d) (hf : f ∈ 𝒜 d) :
    (projSectionMapDomain 𝒜 L ψ).ι ''ᵁ (c.map ⁻¹ᵁ Proj.basicOpen 𝒜 f) =
      (inferInstance : Invertible L).nonvanishingOpen
        (projSectionMapDegreeSection 𝒜 L ψ d ⟨f, hf⟩) :=
  hc.1 hd hf

/-- The degreewise square from homogeneous elements to restricted tensor-power sections
commutes. -/
theorem degree_commutes {c : ProjSectionMap 𝒜 L P ψ} (hc : c.IsCanonical)
    (d : ℕ) (x : 𝒜 d) :
    ((P.actualSectionMap d ≫
        globalSectionsPullback c.map (P.actualTwist (d : ℤ)) ≫
        globalSectionsMap (c.component (d : ℤ))).hom) x =
      ((globalSectionsMap
          (@RingedSpace.InvertiblePower.natIso _ L
            (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L)) d).hom ≫
        globalSectionsPullback (projSectionMapDomain 𝒜 L ψ).ι
          (tensorPowerInt L (d : ℤ))).hom)
        (projSectionMapDegreeSection 𝒜 L ψ d x) :=
  hc.2 d x

end IsCanonical

end ProjSectionMap

/-- Every graded section map and explicit twist presentation determine a unique complete
canonical projective section map. -/
theorem existsUnique_projSectionMap
    (P : ProjTwistPresentation 𝒜)
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L) :
    ∃! c : ProjSectionMap 𝒜 L P ψ, c.IsCanonical := sorry

/-- The degree-`d` tensor power of an invertible module restricted to an open subscheme. -/
noncomputable abbrev restrictedVeroneseLineBundle
    (V : T.Opens) (d : ℕ) : V.toScheme.Modules :=
  (Scheme.Modules.pullback V.ι).obj (RingedSpace.TensorPower.sheaf L d)

/-- The restriction of a nonnegative tensor power of an invertible module to an open subscheme
is invertible. -/
instance restrictedVeroneseLineBundle_isInvertible
    (V : T.Opens) (d : ℕ) : Invertible (restrictedVeroneseLineBundle L V d) :=
  Invertible.pullback V.ι
    (Invertible.tensorPower_isInvertible (inferInstance : Invertible L) d)

/-- The canonical comparison between powers of a restricted degree-`d` tensor power and the
restrictions of the corresponding degree-`n * d` tensor powers. -/
noncomputable def restrictedVeronesePowerIso (V : T.Opens) (d n : ℕ) :
    RingedSpace.TensorPower.sheaf (restrictedVeroneseLineBundle L V d) n ≅
      (Scheme.Modules.pullback V.ι).obj (RingedSpace.TensorPower.sheaf L (n * d)) :=
  RingedSpace.TensorPower.mapIso (pullbackTensorPowerIso V.ι L d) n ≪≫
    RingedSpace.TensorPower.mulIso ((Scheme.Modules.pullback V.ι).obj L) d n ≪≫
    (pullbackTensorPowerIso V.ι L (n * d)).symm

/-- The degree-`n` component of a graded section map, restricted to an open and transported to
the `n`th power of the restricted degree-`d` tensor power. -/
noncomputable def restrictedVeroneseDegreeMap
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (V : T.Opens) (d n : ℕ) :
    𝒜 (n * d) →+
      RingedSpace.GradedSections.ring (restrictedVeroneseLineBundle L V d) :=
  (DirectSum.of
      (RingedSpace.GradedSections.degree (restrictedVeroneseLineBundle L V d)) n).comp
    ((globalSectionsMap (restrictedVeronesePowerIso L V d n).inv).hom.comp
      ((globalSectionsPullback V.ι
          (RingedSpace.TensorPower.sheaf L (n * d))).hom.comp
        ((DirectSum.InternalGrading.summandEquiv
            (RingedSpace.GradedSections.degree L) (n * d)).symm.toAddMonoidHom.comp
          (ψ.gradedAddHom (n * d)))))

/-- The additive map obtained by assembling all canonically restricted Veronese degrees. -/
noncomputable def restrictedVeroneseSectionMapAddHom
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (V : T.Opens) (d : ℕ) :
    GradedRing.Veronese 𝒜 d →+
      RingedSpace.GradedSections.ring (restrictedVeroneseLineBundle L V d) :=
  DirectSum.toAddMonoid fun n ↦ restrictedVeroneseDegreeMap 𝒜 L ψ V d n

/-- The assembled restricted Veronese additive map preserves the multiplicative unit. -/
theorem restrictedVeroneseSectionMapAddHom_one
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (V : T.Opens) (d : ℕ) :
    restrictedVeroneseSectionMapAddHom 𝒜 L ψ V d 1 = 1 := sorry

/-- The assembled restricted Veronese additive map preserves multiplication. -/
theorem restrictedVeroneseSectionMapAddHom_mul
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (V : T.Opens) (d : ℕ) (x y : GradedRing.Veronese 𝒜 d) :
    restrictedVeroneseSectionMapAddHom 𝒜 L ψ V d (x * y) =
      restrictedVeroneseSectionMapAddHom 𝒜 L ψ V d x *
        restrictedVeroneseSectionMapAddHom 𝒜 L ψ V d y := sorry

/-- The canonical ring homomorphism obtained by restricting a graded section map to the
`d`th Veronese ring over an open subscheme. -/
noncomputable def restrictedVeroneseSectionMap
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (V : T.Opens) (d : ℕ) :
    GradedRing.Veronese 𝒜 d →+*
      RingedSpace.GradedSections.ring (restrictedVeroneseLineBundle L V d) where
  toFun := restrictedVeroneseSectionMapAddHom 𝒜 L ψ V d
  map_zero' := map_zero (restrictedVeroneseSectionMapAddHom 𝒜 L ψ V d)
  map_add' := map_add (restrictedVeroneseSectionMapAddHom 𝒜 L ψ V d)
  map_one' := restrictedVeroneseSectionMapAddHom_one 𝒜 L ψ V d
  map_mul' := restrictedVeroneseSectionMapAddHom_mul 𝒜 L ψ V d

/-- On a pure homogeneous input, the canonical restricted Veronese homomorphism is its
canonically restricted and transported degree map. -/
theorem restrictedVeroneseSectionMap_of
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (V : T.Opens) (d n : ℕ) (x : 𝒜 (n * d)) :
    restrictedVeroneseSectionMap 𝒜 L ψ V d
        (DirectSum.of (GradedRing.Veronese.degree 𝒜 d) n x) =
      restrictedVeroneseDegreeMap 𝒜 L ψ V d n x := sorry

/-- A Veronese section map on an open subscheme is the restriction of a graded section map when
each homogeneous component is obtained by canonical pullback and tensor-power comparison. -/
def IsRestrictedVeroneseSectionMap
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (V : T.Opens) (d : ℕ)
    (ψVd : GradedRing.Veronese 𝒜 d →+*
      RingedSpace.GradedSections.ring (restrictedVeroneseLineBundle L V d)) : Prop :=
  ∀ n (x : 𝒜 (n * d)),
    (globalSectionsMap (restrictedVeronesePowerIso L V d n).hom).hom
        ((ψVd (DirectSum.of (GradedRing.Veronese.degree 𝒜 d) n x)) n) =
      (globalSectionsPullback V.ι
        (RingedSpace.TensorPower.sheaf L (n * d))).hom
          (projSectionMapDegreeSection 𝒜 L ψ (n * d) x)

/-- The canonical restricted Veronese homomorphism has the prescribed pullback-and-transport
description in every degree. -/
theorem restrictedVeroneseSectionMap_isRestricted
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (V : T.Opens) (d : ℕ) :
    IsRestrictedVeroneseSectionMap 𝒜 L ψ V d
      (restrictedVeroneseSectionMap 𝒜 L ψ V d) := sorry

/-- A Veronese section homomorphism is the canonical restriction exactly when each homogeneous
component is obtained by the prescribed pullback and tensor-power comparison. -/
theorem isRestrictedVeroneseSectionMap_iff
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (V : T.Opens) (d : ℕ)
    (ψVd : GradedRing.Veronese 𝒜 d →+*
      RingedSpace.GradedSections.ring (restrictedVeroneseLineBundle L V d)) :
    IsRestrictedVeroneseSectionMap 𝒜 L ψ V d ψVd ↔
      ψVd = restrictedVeroneseSectionMap 𝒜 L ψ V d := sorry

/-- A canonically restricted Veronese section map preserves its homogeneous grading. -/
theorem restrictedVeroneseSectionMap_preservesDegree
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (V : T.Opens) (d : ℕ)
    (ψVd : GradedRing.Veronese 𝒜 d →+*
      RingedSpace.GradedSections.ring (restrictedVeroneseLineBundle L V d))
    (hψVd : IsRestrictedVeroneseSectionMap 𝒜 L ψ V d ψVd) :
    veroneseSectionMapPreservesDegree 𝒜 d (restrictedVeroneseLineBundle L V d) ψVd := sorry

/-- If the degree-one image of a restricted Veronese section map generates, then its open lies
inside the natural domain of the original graded section map. -/
theorem degreeImageGenerates_le_projSectionMapDomain
    (ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L)
    (V : T.Opens) (d : ℕ) (hd : 1 ≤ d)
    (ψVd : GradedRing.Veronese 𝒜 d →+*
      RingedSpace.GradedSections.ring (restrictedVeroneseLineBundle L V d))
    (hψVd : IsRestrictedVeroneseSectionMap 𝒜 L ψ V d ψVd)
    (hgen : veroneseDegreeOneImageGenerates 𝒜 d
      (restrictedVeroneseLineBundle L V d) ψVd) :
    V ≤ projSectionMapDomain 𝒜 L ψ := sorry

namespace ProjSectionMap

variable {𝒜 L}
variable {P : ProjTwistPresentation 𝒜}
variable {ψ : 𝒜 →+*ᵍ RingedSpace.GradedSections.grading L}

/-- The degree-`d` component of a projective section map, restricted to a smaller open and
transported to the restricted degree-`d` tensor power. -/
noncomputable def restrictedComponent
    (c : ProjSectionMap 𝒜 L P ψ)
    (V : T.Opens) (hV : V ≤ projSectionMapDomain 𝒜 L ψ) (d : ℕ) (hd : 1 ≤ d)
    {φd : V.toScheme ⟶ (Proj.degreeOpen 𝒜 d).toScheme}
    (hcomp : T.homOfLE hV ≫ c.map = φd ≫ (Proj.degreeOpen 𝒜 d).ι) :
    Proj.DegreeOpenFactorization.lineBundle 𝒜 P
        ({ degree := d, positive := hd, map := φd } :
          Proj.DegreeOpenFactorization 𝒜 V.toScheme) ⟶
      restrictedVeroneseLineBundle L V d :=
  ((Scheme.Modules.pullbackCongr hcomp.symm).hom.app (P.actualTwist d)) ≫
    ((Scheme.Modules.pullbackComp (T.homOfLE hV) c.map).inv.app
      (P.actualTwist d)) ≫
    (Scheme.Modules.pullback (T.homOfLE hV)).map (c.component (d : ℤ)) ≫
    ((Scheme.Modules.pullbackComp (T.homOfLE hV)
      (projSectionMapDomain 𝒜 L ψ).ι).hom.app (tensorPowerInt L (d : ℤ))) ≫
    ((Scheme.Modules.pullbackCongr (T.homOfLE_ι hV)).hom.app
      (tensorPowerInt L (d : ℤ))) ≫
    (Scheme.Modules.pullback V.ι).map
      (@RingedSpace.InvertiblePower.natIso _ L
        (Invertible.ringedSpaceIsInvertible (inferInstance : Invertible L)) d).inv

namespace IsCanonical

/-- On an open generated by positive degree-`d` images, the restricted canonical morphism and
its degree-`d` comparison are the unique degree-open morphism and twist isomorphism associated
to the restricted Veronese section map. -/
theorem restrict_eq_degreeOpenMorphismAndTwistIso
    {c : ProjSectionMap 𝒜 L P ψ} (hc : c.IsCanonical)
    (V : T.Opens) (d : ℕ) (hd : 1 ≤ d)
    (hgen : veroneseDegreeOneImageGenerates 𝒜 d
      (restrictedVeroneseLineBundle L V d)
        (restrictedVeroneseSectionMap 𝒜 L ψ V d)) :
    ∃ hV : V ≤ projSectionMapDomain 𝒜 L ψ,
      ∃! φd : V.toScheme ⟶ (Proj.degreeOpen 𝒜 d).toScheme,
        let x : Proj.DegreeOpenFactorization 𝒜 V.toScheme :=
          { degree := d, positive := hd, map := φd }
        ∃! α : Proj.DegreeOpenFactorization.lineBundle 𝒜 P x ≅
            restrictedVeroneseLineBundle L V d,
          Proj.DegreeOpenFactorization.SectionMapCompatible 𝒜 P x
              (restrictedVeroneseLineBundle L V d)
                (restrictedVeroneseSectionMap 𝒜 L ψ V d) α ∧
            ∃ hcomp : T.homOfLE hV ≫ c.map = φd ≫ (Proj.degreeOpen 𝒜 d).ι,
              c.restrictedComponent V hV d hd hcomp = α.hom := sorry

end IsCanonical

end ProjSectionMap

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {T : Scheme.{u}} (L : T.Modules) [Scheme.Modules.Invertible L]

/-- The additive projection from a tensor-power section ring onto its degree-`d` summand. -/
noncomputable abbrev tensorPowerSectionRingProj (L : T.Modules) (d : ℕ) :
    RingedSpace.GradedSections.ring L →+ Γ(RingedSpace.TensorPower.sheaf L d, ⊤) :=
  (DirectSum.component ℤ ℕ (RingedSpace.GradedSections.degree L) d).toAddMonoidHom

/-- A raw ring homomorphism into a tensor-power section ring preserves the grading when every
homogeneous input belongs to the corresponding internal homogeneous summand. -/
def projSectionRingMapPreservesDegree
    (ψ : A →+* RingedSpace.GradedSections.ring L) : Prop :=
  ∀ d (x : 𝒜 d), ψ x.1 ∈ RingedSpace.GradedSections.grading L d

/-- A grading-preserving raw section-ring homomorphism as a bundled graded ring homomorphism. -/
def projSectionRingGradedHom
    (ψ : A →+* RingedSpace.GradedSections.ring L)
    (hgraded : projSectionRingMapPreservesDegree 𝒜 L ψ) :
    𝒜 →+*ᵍ RingedSpace.GradedSections.grading L where
  toRingHom := ψ
  map_mem := fun {i x} hx ↦ hgraded i ⟨x, hx⟩

/-- The degree-`d` tensor-power section represented by the image of a homogeneous element. -/
noncomputable abbrev projSectionRingDegreeSection
    (ψ : A →+* RingedSpace.GradedSections.ring L) (d : ℕ) (x : 𝒜 d) :
    Γ(RingedSpace.TensorPower.sheaf L d, ⊤) :=
  tensorPowerSectionRingProj L d (ψ x.1)

/-- The natural domain of a grading-preserving raw section-ring homomorphism. -/
noncomputable abbrev projSectionRingDomain
    (ψ : A →+* RingedSpace.GradedSections.ring L)
    (hgraded : projSectionRingMapPreservesDegree 𝒜 L ψ) : T.Opens :=
  Scheme.Modules.projSectionMapDomain 𝒜 L
    (projSectionRingGradedHom 𝒜 L ψ hgraded)

/-- The complete projective section-map datum associated to a grading-preserving raw ring
homomorphism. -/
abbrev ProjSectionRingMorphism
    (P : ProjTwistPresentation 𝒜)
    (ψ : A →+* RingedSpace.GradedSections.ring L)
    (hgraded : projSectionRingMapPreservesDegree 𝒜 L ψ) :=
  Scheme.Modules.ProjSectionMap 𝒜 L P
    (projSectionRingGradedHom 𝒜 L ψ hgraded)

/-- A projective section-map datum is compatible with a raw section-ring homomorphism when it
is canonical for the associated bundled graded homomorphism. -/
abbrev projSectionRingMorphismCompatible
    (P : ProjTwistPresentation 𝒜)
    (ψ : A →+* RingedSpace.GradedSections.ring L)
    (hgraded : projSectionRingMapPreservesDegree 𝒜 L ψ)
    (c : ProjSectionRingMorphism 𝒜 L P ψ hgraded) : Prop :=
  Scheme.Modules.ProjSectionMap.IsCanonical c

end AlgebraicGeometry
