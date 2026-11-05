module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CellReplacement
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Basic
public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.QuasiIso
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat.BoundedAbove
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.TermwiseFlat.QuasiIso

/-!
# K-flat resolutions on a ringed site

Complexes of modules over a commutative ring sheaf admit termwise epimorphic K-flat resolutions
with flat terms.  The final declaration connects this geometric existence theorem to the generic
localizer-resolution interface used by monoidal derived localization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.KFlat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}
section Canonical

variable [UnivLE.{max u v, w}]

private theorem presheafAugmentation_epi
    (G : CochainComplex (PresheafOfModules.{w} (ringSheaf J O).obj) ℤ) (n : ℤ) :
    Epi ((PresheafOfModules.CellReplacement.augmentation G).f n) := by
  apply PresheafOfModules.epi_of_surjective
  intro U x
  let c : PresheafOfModules.CellReplacement.Cell
      (PresheafOfModules.CellReplacement.seed G).augmentation (n + 1) U :=
    { x := (G.d n (n + 1)).app U x
      y := 0
      dx := by
        change ((G.d n (n + 1) ≫ G.d (n + 1) ((n + 1) + 1)).app U) x = 0
        rw [G.d_comp_d]
        rfl
      dy := by simp }
  let y := (biprod.inr : _ ⟶
    PresheafOfModules.CellReplacement.nextTerm
      (PresheafOfModules.CellReplacement.seed G).augmentation (n + 1)).app U
        (ModuleCat.freeMk c)
  let c' : PresheafOfModules.CellReplacement.Cell
      (PresheafOfModules.CellReplacement.stage G 1).augmentation n U :=
    { x := x
      y := y
      dx := by
        exact (PresheafOfModules.CellReplacement.augmentation_generator
          (PresheafOfModules.CellReplacement.seed G).augmentation (n + 1) U c).symm
      dy := by
        dsimp [y, PresheafOfModules.CellReplacement.stage,
          PresheafOfModules.CellReplacement.Stage.next,
          PresheafOfModules.CellReplacement.nextComplex]
        rw [CochainComplex.of_d]
        change ((biprod.inr ≫
          PresheafOfModules.CellReplacement.nextDifferential
            (PresheafOfModules.CellReplacement.seed G).augmentation (n + 1)).app U)
              (ModuleCat.freeMk c) = 0
        unfold PresheafOfModules.CellReplacement.nextDifferential
        rw [biprod.inr_desc]
        change ((biprod.inl :
          (PresheafOfModules.CellReplacement.seed G).complex.X ((n + 1) + 1) ⟶
          PresheafOfModules.CellReplacement.nextTerm
            (PresheafOfModules.CellReplacement.seed G).augmentation ((n + 1) + 1)).app U)
          ((PresheafOfModules.CellReplacement.evaluateY
            (PresheafOfModules.CellReplacement.seed G).augmentation (n + 1)).app U
              (ModuleCat.freeMk c)) = 0
        dsimp only [PresheafOfModules.CellReplacement.evaluateY,
          PresheafOfModules.freeObjDesc]
        erw [ModuleCat.freeDesc_apply]
        exact map_zero _ }
  let z := (biprod.inr : _ ⟶
    PresheafOfModules.CellReplacement.nextTerm
      (PresheafOfModules.CellReplacement.stage G 1).augmentation n).app U
        (ModuleCat.freeMk c')
  refine ⟨((colimit.ι (PresheafOfModules.CellReplacement.diagram G) 2).f n).app U z, ?_⟩
  have h := PresheafOfModules.CellReplacement.stage_augmentation G 2
  have hn := congrArg (fun f => (f.f n).app U) h
  have hx := ConcreteCategory.congr_hom hn z
  exact hx.trans (PresheafOfModules.CellReplacement.augmentation_generator
    (PresheafOfModules.CellReplacement.stage G 1).augmentation n U c')

private theorem additiveSheafify : HasSheafify J AddCommGrpCat.{w} := by
  have : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (CategoryTheory.forget AddCommGrpCat.{w}) :=
    preservesFilteredColimitsOfSize_of_univLE (CategoryTheory.forget AddCommGrpCat.{w})
  infer_instance

private theorem augmentation_epi
    (G : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) (n : ℤ) :
    Epi ((SheafOfModules.CellReplacement.augmentation G).f n) := by
  have : Epi ((SheafOfModules.CellReplacement.presheafAugmentation G).f n) :=
    presheafAugmentation_epi (SheafOfModules.CellReplacement.underlying G) n
  change Epi (((PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 (ringSheaf J O).obj)).homEquiv _ _).symm _)
  rw [Adjunction.homEquiv_counit]
  have hmap : Epi ((PresheafOfModules.sheafification (𝟙 (ringSheaf J O).obj)).map
      ((SheafOfModules.CellReplacement.presheafAugmentation G).f n)) :=
    Functor.map_epi _ _
  have : IsIso (PresheafOfModules.sheafificationAdjunction.{w}
      (𝟙 (ringSheaf J O).obj)).counit := inferInstance
  have : IsIso ((PresheafOfModules.sheafificationAdjunction.{w}
      (𝟙 (ringSheaf J O).obj)).counit.app (G.X n)) := inferInstance
  apply (epi_comp_iff_of_isIso _ ((PresheafOfModules.sheafificationAdjunction.{w}
      (𝟙 (ringSheaf J O).obj)).counit.app (G.X n))).mpr
  exact hmap

/-- Every complex of modules on a ringed site admits a termwise epimorphic quasi-isomorphism
from a K-flat, termwise-flat complex. -/
@[stacks 06YS "termwise epimorphic K-flat resolution"]
theorem exists_termwiseEpi_resolution
    (G : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) :
    ∃ (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) (f : K ⟶ G),
      K.IsKFlat ∧ HomologicalComplex.IsTermwiseFlat K ∧ QuasiIso f ∧
        ∀ n : ℤ, Epi (f.f n) := by
  have := additiveSheafify (J := J)
  exact ⟨SheafOfModules.CellReplacement.model G,
    SheafOfModules.CellReplacement.augmentation G,
    CellReplacement.model_isKFlat G, CellReplacement.model_termwiseFlat G,
    SheafOfModules.CellReplacement.augmentation_quasiIso G, augmentation_epi G⟩

/-- Every complex of modules on a ringed site admits an epimorphic quasi-isomorphism from a
K-flat, termwise-flat complex. -/
theorem exists_epi_resolution
    (G : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) :
    ∃ (K : CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ) (f : K ⟶ G),
      K.IsKFlat ∧ HomologicalComplex.IsTermwiseFlat K ∧ QuasiIso f ∧ Epi f := by
  obtain ⟨K, f, hK, hflat, hq, hepi⟩ := exists_termwiseEpi_resolution G
  exact ⟨K, f, hK, hflat, hq, HomologicalComplex.epi_of_epi_f f hepi⟩

/-- Modules on a ringed site have resolutions by K-flat complexes with flat terms, in the
canonical localizer-morphism sense.  Unlike the coarser `KFlat.HasResolutions` instance, this
owner retains the termwise-flat condition needed by pullback arguments. -/
@[stacks 06YS "K-flat termwise-flat resolutions"]
theorem termwiseFlatHasResolutions :
    HomotopyCategory.KFlat.TermwiseFlat.HasResolutions
      (ringedSiteModuleCategory.{u, v, w, w} J O) := by
  intro X
  obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨K, f, hK, hflat, hq, hepi⟩ := exists_termwiseEpi_resolution (O := O) G
  refine ⟨{ X₁ := ⟨(HomotopyCategory.quotient _ _).obj K, ⟨hK, hflat⟩⟩
            w := (HomotopyCategory.quotient _ _).map f
            hw := ?_ }⟩
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr hq

/-- Modules on a ringed site have K-flat resolutions in the canonical localizer sense. -/
@[stacks 0FPB "ringed-site K-flat resolutions"]
instance hasResolutions :
    HomotopyCategory.KFlat.HasResolutions
      (ringedSiteModuleCategory.{u, v, w, w} J O) := by
  intro X
  obtain ⟨r⟩ := termwiseFlatHasResolutions (O := O) X
  exact ⟨{ X₁ := ⟨r.X₁.obj, r.X₁.property.1⟩, w := r.w, hw := r.hw }⟩

end Canonical

variable [UnivLE.{max u v, z}]

variable [Abelian (ringedSiteModuleCategory.{u, v, z, w} J O)]
variable [CategoryWithHomology (ringedSiteModuleCategory.{u, v, z, w} J O)]
variable [MonoidalCategory (ringedSiteModuleCategory.{u, v, z, w} J O)]
variable [MonoidalPreadditive (ringedSiteModuleCategory.{u, v, z, w} J O)]


namespace TermwiseFlat

/-- A bounded-above homotopy complex of modules with flat terms belongs to the canonical
subcategory of K-flat termwise-flat models. -/
@[stacks 06YQ "ringed-site bounded-above good models"]
theorem of_boundedAbove
    {K : HomotopyCategory (ringedSiteModuleCategory.{u, v, z, w} J O)
      (ComplexShape.up ℤ)}
    (hFlat : HomologicalComplex.IsTermwiseFlat K.as)
    (hbounded : CochainComplex.minus
      (ringedSiteModuleCategory.{u, v, z, w} J O) K.as) :
    HomotopyCategory.KFlat.termwiseFlat
      (ringedSiteModuleCategory.{u, v, z, w} J O) K := sorry

end TermwiseFlat

end SheafOfModules.RingedSite.KFlat
