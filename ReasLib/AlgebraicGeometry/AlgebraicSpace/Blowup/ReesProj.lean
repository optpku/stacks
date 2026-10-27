/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Rees.Blowup
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Rees projective spectra on affine étale charts

Restricted section ideals determine Rees projective schemes with their canonical
structure morphisms and affine homogeneous-localization chart coverings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- The ideal of global functions on an affine étale chart corresponding to the
restriction of a quasi-coherent ideal sheaf. -/
def correspondingIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X) :
    Ideal Γ(U.obj.left.left, ⊤) :=
  IdealSheaf.sections (Modules.toCommSubobject I) (op U.obj)

/-- `correspondingIdeal I U` is the section ideal of `I` on the underlying étale
object of `U`. -/
theorem correspondingIdeal_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X) :
    correspondingIdeal I U =
      IdealSheaf.sections (Modules.toCommSubobject I) (op U.obj) :=
  rfl

/-- Membership in `correspondingIdeal I U` is membership in the section ideal of
`I` on the underlying étale object of `U`. -/
theorem mem_correspondingIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X)
    (x : Γ(U.obj.left.left, ⊤)) :
    x ∈ correspondingIdeal I U ↔
      x ∈ IdealSheaf.sections (Modules.toCommSubobject I) (op U.obj) :=
  Iff.rfl

/-- The homogeneous spectrum of the Rees algebra of `correspondingIdeal I U`. -/
abbrev reesProj {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) : Scheme.{u} :=
  Proj (ReesAlgebra.Grading.grade (correspondingIdeal I U))

/-- `reesProj I U` is `Proj` of the canonical grading of the Rees algebra of
`correspondingIdeal I U`. -/
theorem reesProj_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) :
    reesProj I U = Proj (ReesAlgebra.Grading.grade (correspondingIdeal I U)) :=
  rfl

/-- The structure morphism of `reesProj I U` over the affine étale chart `U`. -/
def reesProjToU {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) : reesProj I U ⟶ U.obj.left.left :=
  ReesProj.toSpec (correspondingIdeal I U) ≫ U.obj.left.left.isoSpec.inv

/-- `reesProjToU` is `ReesProj.toSpec` followed by the inverse of `Scheme.isoSpec`
on the affine étale chart. -/
theorem reesProjToU_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X) :
    reesProjToU I U =
      ReesProj.toSpec (correspondingIdeal I U) ≫ U.obj.left.left.isoSpec.inv :=
  rfl

/-- The homogeneous spectrum of the restricted Rees algebra, as a scheme over `S`. -/
def reesProjOver {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) : Over S :=
  Over.mk (reesProjToU I U ≫ U.obj.left.hom)

/-- The underlying scheme of `reesProjOver I U` is `reesProj I U`. -/
theorem reesProjOver_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X) :
    (reesProjOver I U).left = reesProj I U :=
  rfl

/-- The morphism of algebraic spaces over `S` induced by `reesProjToU`. -/
def reesProjOverToU {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) :
    ofOver (reesProjOver I U) ⟶ ofOver U.obj.left :=
  ofOverMap (Over.homMk (reesProjToU I U) rfl)

/-- `reesProjOverToU` is `ofOverMap` of the over-morphism induced by `reesProjToU`. -/
theorem reesProjOverToU_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X) :
    reesProjOverToU I U = ofOverMap (Over.homMk (reesProjToU I U) rfl) :=
  rfl

/-- The canonical open immersion of the affine blowup chart associated to `a` into
`reesProj I U`. -/
def affineChartι {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) (a : correspondingIdeal I U) :
    Spec (.of (affineBlowupChart (correspondingIdeal I U) a)) ⟶ reesProj I U :=
  Proj.awayι (ReesAlgebra.Grading.grade (correspondingIdeal I U))
    (ReesAlgebra.Grading.degreeOne (correspondingIdeal I U) a)
    (ReesAlgebra.Grading.degreeOne_mem (correspondingIdeal I U) a) Nat.zero_lt_one

/-- `affineChartι I U a` is `Proj.awayι` of the degree-one Rees element `a`. -/
theorem affineChartι_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) (a : correspondingIdeal I U) :
    affineChartι I U a =
      Proj.awayι (ReesAlgebra.Grading.grade (correspondingIdeal I U))
        (ReesAlgebra.Grading.degreeOne (correspondingIdeal I U) a)
        (ReesAlgebra.Grading.degreeOne_mem (correspondingIdeal I U) a) Nat.zero_lt_one :=
  rfl

/-- The structure morphism of an affine blowup chart over the affine étale chart `U`. -/
def affineChartToU {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) (a : correspondingIdeal I U) :
    Spec (.of (affineBlowupChart (correspondingIdeal I U) a)) ⟶ U.obj.left.left :=
  affineChartι I U a ≫ reesProjToU I U

/-- `affineChartToU` is the composite of `affineChartι` with `reesProjToU`. -/
theorem affineChartToU_comp {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (U : affineEtaleSite X) (a : correspondingIdeal I U) :
    affineChartToU I U a = affineChartι I U a ≫ reesProjToU I U :=
  rfl


/-- The over-morphism of an affine blowup chart into `reesProjOver I U`. -/
def affineChartOverHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X)
    (a : correspondingIdeal I U) :
    Over.mk (affineChartToU I U a ≫ U.obj.left.hom) ⟶ reesProjOver I U :=
  Over.homMk (affineChartι I U a) (by exact (Category.assoc _ _ _).symm)

/-- `affineChartOverHom` is `Over.homMk` of `affineChartι`. -/
theorem affineChartOverHom_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (U : affineEtaleSite X)
    (a : correspondingIdeal I U) :
    (affineChartOverHom I U a).left = affineChartι I U a :=
  rfl

/-- Degree-one Rees monomials generate the Rees algebra over its coefficient ring. -/
private theorem reesDegreeOne_adjoin_top {R : Type u} [CommRing R] (I : Ideal R) :
    Algebra.adjoin R (Set.range (ReesAlgebra.Grading.degreeOne I)) = ⊤ := by
  apply Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  convert adjoin_monomial_eq_reesAlgebra I using 2
  ext p
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨a.1, a.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ReesAlgebra.Grading.degreeOne I ⟨a, ha⟩, ⟨_, rfl⟩, rfl⟩

/-- The degree-one basic opens cover the Rees projective spectrum. -/
private theorem reesDegreeOne_basicOpens {R : Type u} [CommRing R] (I : Ideal R) :
    ⨆ a, Proj.basicOpen (ReesAlgebra.Grading.grade I)
      (ReesAlgebra.Grading.degreeOne I a) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · intro a
    exact ⟨1, ReesAlgebra.Grading.degreeOne_mem I a⟩
  · apply top_unique
    intro x hx
    have hx' : x ∈ Algebra.adjoin R (Set.range (ReesAlgebra.Grading.degreeOne I)) := by
      rw [reesDegreeOne_adjoin_top I]
      trivial
    clear hx
    induction hx' using Algebra.adjoin_induction with
    | mem x h => exact Algebra.subset_adjoin h
    | algebraMap r =>
      exact (Algebra.adjoin (ReesAlgebra.Grading.grade I 0)
        (Set.range (ReesAlgebra.Grading.degreeOne I))).algebraMap_mem
          ⟨algebraMap R (reesAlgebra I) r, ReesAlgebra.Grading.algebraMap_mem_zero I r⟩
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy

/-- Every Rees projective point lies in the range of a degree-one affine chart. -/
private theorem reesDegreeOne_charts_cover {R : Type u} [CommRing R] (I : Ideal R)
    (x : Proj (ReesAlgebra.Grading.grade I)) :
    ∃ a : I, x ∈ Set.range (Proj.awayι (ReesAlgebra.Grading.grade I)
      (ReesAlgebra.Grading.degreeOne I a) (ReesAlgebra.Grading.degreeOne_mem I a)
      Nat.zero_lt_one) := by
  have hx : x ∈ (⨆ a, Proj.basicOpen (ReesAlgebra.Grading.grade I)
      (ReesAlgebra.Grading.degreeOne I a)) := (reesDegreeOne_basicOpens I).ge trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨a, ?_⟩
  change x ∈ (Proj.awayι (ReesAlgebra.Grading.grade I)
    (ReesAlgebra.Grading.degreeOne I a) (ReesAlgebra.Grading.degreeOne_mem I a)
    Nat.zero_lt_one).opensRange
  rwa [Proj.opensRange_awayι]

/-- A covering family induces a locally surjective coproduct of representable presheaves. -/
private theorem yonedaSigma_locallySurjective {C : Type*} [Category C]
    (J : GrothendieckTopology C) {ι : Type u} {T : C} {Ti : ι → C}
    (f : ∀ i, Ti i ⟶ T) (hf : Sieve.ofArrows Ti f ∈ J T) :
    Presheaf.IsLocallySurjective J (Sigma.desc (fun i ↦ yoneda.map (f i))) := by
  constructor
  intro V q
  apply J.superset_covering _ (J.pullback_stable q hf)
  rintro W g ⟨Z, p, r, ⟨i⟩, h⟩
  refine ⟨(Sigma.ι (fun i ↦ yoneda.obj (Ti i)) i).app (op W) p, ?_⟩
  have hfac := NatTrans.congr_app (Sigma.ι_desc (fun i ↦ yoneda.map (f i)) i) (op W)
  exact (ConcreteCategory.congr_hom hfac p).trans h

/-- The standard affine blowup charts cover the projective spectrum of the restricted Rees algebra. -/
theorem reesProj_isZariskiCover {S : Scheme.{u}}
    {X : AlgebraicSpace S} {I : IdealSubobject X} [IsQuasiCoherent I]
    (U : affineEtaleSite X) :
    IsZariskiCover (ofOver (reesProjOver I U))
      (fun a : correspondingIdeal I U ↦
        ofOver (Over.mk (affineChartToU I U a ≫ U.obj.left.hom)))
      (fun a ↦ ofOverMap (affineChartOverHom I U a)) := by
  have hopen (a : correspondingIdeal I U) :
      AlgebraicGeometry.IsOpenImmersion (affineChartι I U a) := by
    dsimp [affineChartι]
    infer_instance
  letI : (MorphismProperty.over (X := S) (@AlgebraicGeometry.IsOpenImmersion)).IsStableUnderBaseChange :=
    ⟨fun h hf ↦ MorphismProperty.of_isPullback
      (P := @AlgebraicGeometry.IsOpenImmersion) (h.map (Over.forget S)) hf⟩
  constructor
  · intro a
    exact MorphismProperty.relative_map
      (F := yoneda) (P := MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion))
      (hopen a)
  · apply yonedaSigma_locallySurjective
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    apply Precoverage.generate_mem_toGrothendieck
    apply Scheme.zariskiPrecoverage_le_fppfPrecoverage
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun a ↦ ?_⟩
    · exact reesDegreeOne_charts_cover (correspondingIdeal I U)
    · change AlgebraicGeometry.IsOpenImmersion (affineChartι I U a)
      exact hopen a


end AlgebraicGeometry.AlgebraicSpace.Blowup
