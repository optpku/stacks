module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation

/-!
# Twist-compatible maps of projective spectra

This leaf packages the morphism induced on a natural open domain by a graded ring map together
with comparisons of chosen integral twists.  The small specification lemmas are intentionally
public: downstream construction of composition, base-change, and projective-bundle maps should
not need to unfold the owner structure.

-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open HomogeneousLocalization
open Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {A B sigma tau : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  [CommRing B] [SetLike tau B] [AddSubgroupClass tau B]
  {calA : Nat -> sigma} {calB : Nat -> tau} [GradedRing calA] [GradedRing calB]

/-- A map between projective spectra induced by a graded ring map, equipped with comparison maps
on chosen actual twists and the source-level compatibility conditions they satisfy. -/
structure ProjMap
    (PcalA : ProjTwistPresentation calA)
    (PcalB : ProjTwistPresentation calB)
    (psi : calA →+*ᵍ calB) where
  /-- The map from the natural open domain to the source projective spectrum. -/
  map : (projMapDomain psi).toScheme ⟶ Proj calA
  /-- The degreewise comparison map between the pullback source twist and restricted target twist. -/
  theta :
    forall d : Int,
      (Scheme.Modules.pullback map).obj (PcalA.actualTwist d) ⟶
        (Scheme.Modules.pullback (projMapDomain psi).ι).obj (PcalB.actualTwist d)
  /-- The section comparison square commutes in every nonnegative degree. -/
  degree_commutes :
    forall d : Nat,
      PcalA.actualSectionMap d ≫ globalSectionsPullback map (PcalA.actualTwist d) ≫
          globalSectionsMap (theta d) =
        AddCommGrpCat.ofHom (psi.gradedAddHom d) ≫
          PcalB.actualSectionMap d ≫
            globalSectionsPullback (projMapDomain psi).ι (PcalB.actualTwist d)
  /-- The comparison in degree zero preserves the fixed unit sections. -/
  theta_map_one :
    forall U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ,
      (((theta 0).val.app U).hom) (PcalA.actualOne map U) =
        PcalB.actualOne (projMapDomain psi).ι U
  /-- The comparison maps respect the fixed graded multiplications on sections. -/
  theta_map_mul :
    forall (U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ) (a b : Int)
      (x : pulledBackProjTwistSection PcalA psi map a U)
      (y : pulledBackProjTwistSection PcalA psi map b U),
      (((theta (a + b)).val.app U).hom) (PcalA.actualMul map U a b x y) =
        PcalB.actualMul (projMapDomain psi).ι U a b
          ((((theta a).val.app U).hom) x)
          ((((theta b).val.app U).hom) y)
  /-- Pullback of every positive homogeneous basic open has the expected target basic open. -/
  preimage_basicOpen :
    forall {f : A} {d : Nat}, 0 < d -> f ∈ calA d ->
      (projMapDomain psi).ι ''ᵁ (map ⁻¹ᵁ Proj.basicOpen calA f) = Proj.basicOpen calB (psi f)
  /-- On a basic open, the map agrees with the affine map induced by homogeneous localization. -/
  basicOpenIsoSpec_inv_comp :
    forall {f : A} {d : Nat} (hd : 0 < d) (hf : f ∈ calA d),
      (Proj.basicOpenIsoSpec calB (psi f) (psi.2 hf) hd).inv ≫
          (Proj calB).homOfLE (basicOpen_le_projMapDomain psi hd hf) ≫
            map =
        Spec.map (CommRingCat.ofHom (Away.map psi f)) ≫
          Proj.awayι calA f hf hd

namespace ProjMap

/-- The twist-comparison clauses, stated directly on a candidate map and comparison family. -/
abbrev projMapThetaCompatibility
    (PcalA : ProjTwistPresentation calA)
    (PcalB : ProjTwistPresentation calB)
    (psi : calA →+*ᵍ calB)
    (map : (projMapDomain psi).toScheme ⟶ Proj calA)
    (theta :
      forall d : Int,
        (Scheme.Modules.pullback map).obj (PcalA.actualTwist d) ⟶
          (Scheme.Modules.pullback (projMapDomain psi).ι).obj (PcalB.actualTwist d)) : Prop :=
  (forall d : Nat,
      PcalA.actualSectionMap d ≫ globalSectionsPullback map (PcalA.actualTwist d) ≫
          globalSectionsMap (theta d) =
        AddCommGrpCat.ofHom (psi.gradedAddHom d) ≫
          PcalB.actualSectionMap d ≫
            globalSectionsPullback (projMapDomain psi).ι (PcalB.actualTwist d)) /\
    (forall U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ,
        (((theta 0).val.app U).hom) (PcalA.actualOne map U) =
          PcalB.actualOne (projMapDomain psi).ι U) /\
    forall (U : ((projMapDomain psi).toScheme.Opens)ᵒᵖ) (a b : Int)
      (x : pulledBackProjTwistSection PcalA psi map a U)
      (y : pulledBackProjTwistSection PcalA psi map b U),
      (((theta (a + b)).val.app U).hom) (PcalA.actualMul map U a b x y) =
        PcalB.actualMul (projMapDomain psi).ι U a b
          ((((theta a).val.app U).hom) x)
          ((((theta b).val.app U).hom) y)

/-- The basic-open clauses, stated directly on a candidate map. -/
abbrev projMapBasicOpenCompatibility
    (psi : calA →+*ᵍ calB)
    (map : (projMapDomain psi).toScheme ⟶ Proj calA) : Prop :=
  (forall {f : A} {d : Nat}, 0 < d -> f ∈ calA d ->
      (projMapDomain psi).ι ''ᵁ (map ⁻¹ᵁ Proj.basicOpen calA f) = Proj.basicOpen calB (psi f)) /\
    forall {f : A} {d : Nat} (hd : 0 < d) (hf : f ∈ calA d),
      (Proj.basicOpenIsoSpec calB (psi f) (psi.2 hf) hd).inv ≫
          (Proj calB).homOfLE (basicOpen_le_projMapDomain psi hd hf) ≫
            map =
        Spec.map (CommRingCat.ofHom (Away.map psi f)) ≫
          Proj.awayι calA f hf hd

/-- The complete twist-comparison package carried by a `ProjMap`. -/
theorem theta_compatibility_spec
    {PcalA : ProjTwistPresentation calA}
    {PcalB : ProjTwistPresentation calB}
    {psi : calA →+*ᵍ calB}
    (hProj : ProjMap PcalA PcalB psi) :
    projMapThetaCompatibility PcalA PcalB psi hProj.map hProj.theta :=
  ⟨hProj.degree_commutes, hProj.theta_map_one, hProj.theta_map_mul⟩

/-- The two basic-open compatibility clauses carried by a `ProjMap`. -/
theorem basicOpen_spec
    {PcalA : ProjTwistPresentation calA}
    {PcalB : ProjTwistPresentation calB}
    {psi : calA →+*ᵍ calB}
    (hProj : ProjMap PcalA PcalB psi) :
    projMapBasicOpenCompatibility psi hProj.map :=
  ⟨hProj.preimage_basicOpen, hProj.basicOpenIsoSpec_inv_comp⟩

end ProjMap

/-- A graded ring map induces a map from its natural domain on the target projective spectrum,
together with the twist and basic-open compatibility data recorded by `ProjMap`. -/
noncomputable def projMap
    (PcalA : ProjTwistPresentation calA)
    (PcalB : ProjTwistPresentation calB)
    (psi : calA →+*ᵍ calB) :
    ProjMap PcalA PcalB psi where
  map := projMapMap psi
  theta := projMapTheta PcalA PcalB psi
  degree_commutes :=
    PcalA.presentationMap_degree_commutes PcalB.twistAlgebra psi
  theta_map_one := PcalA.presentationMap_map_one PcalB.twistAlgebra psi
  theta_map_mul := PcalA.presentationMap_map_mul PcalB.twistAlgebra psi
  preimage_basicOpen := projMapMap_preimage_basicOpen psi
  basicOpenIsoSpec_inv_comp := projMapMap_basicOpenIsoSpec_inv_comp psi

namespace ProjMap

/-- Every twist-compatible projective-spectrum map with the prescribed local formulas is the
canonical map associated to its graded ring homomorphism. -/
theorem eq_projMap
    {PcalA : ProjTwistPresentation calA}
    {PcalB : ProjTwistPresentation calB}
    {psi : calA →+*ᵍ calB}
    (hProj : ProjMap PcalA PcalB psi) :
    hProj = projMap PcalA PcalB psi := sorry

end ProjMap

end

end AlgebraicGeometry
