/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map.Chart

/-! # Composition of canonical partial relative-Proj maps -/

@[expose] public section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace SheafOfModules.RingedSite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map

variable {S : Scheme.{u}} {X P Q R : AlgebraicSpace S}
variable {𝒜 ℬ 𝒞 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable {πP : P ⟶ X} {πQ : Q ⟶ X} {πR : R ⟶ X}
variable {twistP : ℤ → P.Modules} {twistQ : ℤ → Q.Modules} {twistR : ℤ → R.Modules}
variable {p : EtalePresentation 𝒜 πP twistP} {q : EtalePresentation ℬ πQ twistQ}
variable {r : EtalePresentation 𝒞 πR twistR}

/-- The inverse-image set inside the second domain, included into the ambient relative Proj. -/
def compDomainSet (rφ : Map p q) (rψ : Map q r) : Set (Points R) :=
  Points.map (OpenSubspace.Construction.ι R rψ.domain) ''
    (Points.map rψ.map ⁻¹' rφ.domain)

/-- The included inverse image of an open under a partial morphism is open. -/
theorem compDomain_isOpen (rφ : Map p q) (rψ : Map q r) :
    IsOpen (compDomainSet rφ rψ) := sorry

/-- The normalized open domain of the restricted composite. -/
def compDomain (rφ : Map p q) (rψ : Map q r) : Opens (Points R) :=
  ⟨compDomainSet rφ rψ, compDomain_isOpen rφ rψ⟩

/-- The composite domain lies in the domain of the second partial morphism. -/
theorem compDomain_le (rφ : Map p q) (rψ : Map q r) :
    compDomain rφ rψ ≤ rψ.domain := sorry

/-- The actual inclusion of the composite domain into the second domain. -/
def compToRight (rφ : Map p q) (rψ : Map q r) :
    OpenSubspace.Construction.space R (compDomain rφ rψ) ⟶
      OpenSubspace.Construction.space R rψ.domain :=
  OpenSubspace.Construction.lift (OpenSubspace.Construction.ι R (compDomain rφ rψ))
    ((OpenSubspace.Construction.inclusion_range R (compDomain rφ rψ)).subset.trans
      (compDomain_le rφ rψ))

/-- The restricted second map has image in the domain of the first map. -/
theorem compToMiddle_range (rφ : Map p q) (rψ : Map q r) :
    Set.range (Points.map (compToRight rφ rψ ≫ rψ.map)) ⊆ rφ.domain := sorry

/-- The second morphism restricted to the inverse image of the first domain. -/
def compToMiddle (rφ : Map p q) (rψ : Map q r) :
    OpenSubspace.Construction.space R (compDomain rφ rψ) ⟶
      OpenSubspace.Construction.space Q rφ.domain :=
  OpenSubspace.Construction.lift (compToRight rφ rψ ≫ rψ.map)
    (compToMiddle_range rφ rψ)

/-- The two routes from the composite domain to the middle relative Proj coincide. -/
theorem compSquare (rφ : Map p q) (rψ : Map q r) :
    compToMiddle rφ rψ ≫ OpenSubspace.Construction.ι Q rφ.domain =
      compToRight rφ rψ ≫ rψ.map := sorry

/-- The restricted composite morphism. -/
def compMap (rφ : Map p q) (rψ : Map q r) :
    OpenSubspace.Construction.space R (compDomain rφ rψ) ⟶ P :=
  compToMiddle rφ rψ ≫ rφ.map

/-- Pull back the first comparison and compose with the second, in each integral degree. -/
def compTheta (rφ : Map p q) (rψ : Map q r) (n : ℤ) :
    (Modules.pullback (compMap rφ rψ)).obj (twistP n) ⟶
      (Modules.pullback (OpenSubspace.Construction.ι R (compDomain rφ rψ))).obj (twistR n) :=
  (Modules.pullbackCompIso (compToMiddle rφ rψ) rφ.map).inv.app (twistP n) ≫
    (Modules.pullback (compToMiddle rφ rψ)).map (rφ.theta n) ≫
    (Modules.pullbackCompIso (compToMiddle rφ rψ)
      (OpenSubspace.Construction.ι Q rφ.domain)).hom.app (twistQ n) ≫
    (Modules.pullbackCongr (compSquare rφ rψ)).hom.app (twistQ n) ≫
    (Modules.pullbackCompIso (compToRight rφ rψ) rψ.map).inv.app (twistQ n) ≫
    (Modules.pullback (compToRight rφ rψ)).map (rψ.theta n) ≫
    (Modules.pullbackCompIso (compToRight rφ rψ)
      (OpenSubspace.Construction.ι R rψ.domain)).hom.app (twistR n) ≫
    (Modules.pullbackCongr (OpenSubspace.Construction.lift_ι
      (OpenSubspace.Construction.ι R (compDomain rφ rψ))
      ((OpenSubspace.Construction.inclusion_range R (compDomain rφ rψ)).subset.trans
        (compDomain_le rφ rψ)))).hom.app (twistR n)

/-- Restricted composition respects the structure maps to the base. -/
theorem compMap_over_base (rφ : Map p q) (rψ : Map q r) :
    compMap rφ rψ ≫ πP = OpenSubspace.Construction.ι R (compDomain rφ rψ) ≫ πR := sorry

/-- Composition of partial relative-Proj morphisms with their integral twist comparisons. -/
def comp (rφ : Map p q) (rψ : Map q r) : Map p r :=
  ofDomain (compDomain rφ rψ) (compMap rφ rψ) (compMap_over_base rφ rψ)
    (compTheta rφ rψ)

/-- Composition of fraction-induced canonical partial maps is canonical for the composite algebra map. -/
theorem isCanonical_comp [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent] [𝒞.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative] [𝒞.IsCommutative]
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (ψ : GradedAlgebraSheaf.Hom.{u + 1, u} ℬ 𝒞)
    (rφ : Map p q) (rψ : Map q r) (hφ : rφ.IsCanonical φ) (hψ : rψ.IsCanonical ψ) :
    (comp rφ rψ).IsCanonical (GradedAlgebraSheaf.Hom.comp.{u + 1, u} φ ψ) := sorry

/-- The independently supplied canonical map for a composite is the restricted composite,
including its open domain and every integral Serre comparison. -/
theorem canonical_comp [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent] [𝒞.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative] [𝒞.IsCommutative]
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (ψ : GradedAlgebraSheaf.Hom.{u + 1, u} ℬ 𝒞)
    (rφ : Map p q) (rψ : Map q r) (rcomp : Map p r)
    (hφ : rφ.IsCanonical φ) (hψ : rψ.IsCanonical ψ)
    (hcomp : rcomp.IsCanonical (GradedAlgebraSheaf.Hom.comp.{u + 1, u} φ ψ)) :
    rcomp = comp rφ rψ := sorry

/-- The canonical composite has the inverse-image open domain. -/
theorem canonical_comp_domain [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent] [𝒞.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative] [𝒞.IsCommutative]
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (ψ : GradedAlgebraSheaf.Hom.{u + 1, u} ℬ 𝒞)
    (rφ : Map p q) (rψ : Map q r) (rcomp : Map p r)
    (hφ : rφ.IsCanonical φ) (hψ : rψ.IsCanonical ψ)
    (hcomp : rcomp.IsCanonical (GradedAlgebraSheaf.Hom.comp.{u + 1, u} φ ψ)) :
    rcomp.domain = compDomain rφ rψ := sorry

/-- Transport a morphism along equality of its normalized open source. -/
def mapOnDomain {D E : Opens (Points R)} (h : D = E)
    (f : OpenSubspace.Construction.space R E ⟶ P) :
    OpenSubspace.Construction.space R D ⟶ P :=
  match h with | rfl => f

/-- The canonical composite morphism is the restricted composite after domain transport. -/
theorem canonical_comp_map [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent] [𝒞.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative] [𝒞.IsCommutative]
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (ψ : GradedAlgebraSheaf.Hom.{u + 1, u} ℬ 𝒞)
    (rφ : Map p q) (rψ : Map q r) (rcomp : Map p r)
    (hφ : rφ.IsCanonical φ) (hψ : rψ.IsCanonical ψ)
    (hcomp : rcomp.IsCanonical (GradedAlgebraSheaf.Hom.comp.{u + 1, u} φ ψ)) :
    rcomp.map = mapOnDomain (canonical_comp_domain φ ψ rφ rψ rcomp hφ hψ hcomp)
      (compMap rφ rψ) := sorry

/-- Transport an integral twist comparison along equality of normalized domains. -/
def thetaOnDomain {D E : Opens (Points R)} (h : D = E)
    (f : OpenSubspace.Construction.space R E ⟶ P) (n : ℤ)
    (theta : (Modules.pullback f).obj (twistP n) ⟶
      (Modules.pullback (OpenSubspace.Construction.ι R E)).obj (twistR n)) :
    (Modules.pullback (mapOnDomain h f)).obj (twistP n) ⟶
      (Modules.pullback (OpenSubspace.Construction.ι R D)).obj (twistR n) :=
  (Eq.recOn h (motive := fun E h ↦
    ∀ (f : OpenSubspace.Construction.space R E ⟶ P),
      ((Modules.pullback f).obj (twistP n) ⟶
        (Modules.pullback (OpenSubspace.Construction.ι R E)).obj (twistR n)) →
      ((Modules.pullback (mapOnDomain h f)).obj (twistP n) ⟶
        (Modules.pullback (OpenSubspace.Construction.ι R D)).obj (twistR n)))
    (fun _ theta ↦ theta)) f theta

/-- In every integral degree the canonical composite comparison is the pullback-and-compose map. -/
theorem canonical_comp_theta [𝒜.IsQuasicoherent] [ℬ.IsQuasicoherent] [𝒞.IsQuasicoherent]
    [𝒜.IsCommutative] [ℬ.IsCommutative] [𝒞.IsCommutative]
    (φ : GradedAlgebraSheaf.Hom.{u + 1, u} 𝒜 ℬ)
    (ψ : GradedAlgebraSheaf.Hom.{u + 1, u} ℬ 𝒞)
    (rφ : Map p q) (rψ : Map q r) (rcomp : Map p r)
    (hφ : rφ.IsCanonical φ) (hψ : rψ.IsCanonical ψ)
    (hcomp : rcomp.IsCanonical (GradedAlgebraSheaf.Hom.comp.{u + 1, u} φ ψ)) (n : ℤ) :
    rcomp.theta n =
      (Modules.pullbackCongr (canonical_comp_map φ ψ rφ rψ rcomp hφ hψ hcomp)).hom.app
          (twistP n) ≫
        thetaOnDomain (canonical_comp_domain φ ψ rφ rψ rcomp hφ hψ hcomp)
          (compMap rφ rψ) n (compTheta rφ rψ n) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.Map
