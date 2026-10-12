/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Constructed factories for the canonical forward comparison

All declarations in this module have proved construction certificates. The
presheaf extension is Mathlib's free-generator construction on an explicit
`AsSmall` reindexing. This changes the presentation of the indexing categories,
never the universe of the module carriers. Sheafification uses the proved plus
construction at the actual size of the site.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
universe u v

namespace Stacks1048Forward

/-- Plus construction at the site-sized coefficient universe. -/
theorem certifiedSheafify {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) : HasSheafify J AddCommGrpCat.{max u v} := by
  infer_instance

/-- The weak certificate is projected from the proved plus construction. -/
theorem certifiedWeakSheafify {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) : HasWeakSheafify J AddCommGrpCat.{max u v} :=
  (certifiedSheafify J).isRightAdjoint

/-- The actual morphism-local criterion of the same plus construction. -/
theorem certifiedLocallyBijective {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) : J.WEqualsLocallyBijective AddCommGrpCat.{max u v} := by
  infer_instance

/-- The abelian-category structure is transferred along the proved sheafification
adjunction, including its actual finite-limit and finite-colimit existence certificates. -/
def certifiedModuleAbelian {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{max u v}) :
    Abelian (SheafOfModules.{max u v} R) := by
  -- Local instance justification (instance diamond): the transfer uses the proved plus construction rather than a chapter-level admitted category structure.
  letI := certifiedSheafify J
  -- Local instance justification (instance diamond): certify the locally-bijective morphism property for that same sheafification.
  letI := certifiedLocallyBijective J
  infer_instance

/-- Sheafify an actual module presheaf over the fixed ring sheaf. This closed
Mathlib-only factory pins the full proved sheafification construction before
any geometric presentation can introduce competing instance candidates. -/
def certifiedModuleSheafification {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{max u v}) :
    PresheafOfModules.{max u v} R.obj ⥤ SheafOfModules.{max u v} R := by
  -- Local instance justification (instance diamond): use the proved site-sized sheafification construction in this closed factory.
  letI := certifiedWeakSheafify J
  -- Local instance justification (instance diamond): use the matching proved locally-bijective criterion for the identity coefficient morphism.
  letI := certifiedLocallyBijective J
  exact PresheafOfModules.sheafification (R := R) (𝟙 R.obj)

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Reindexing and its reverse retain the same section carriers and maps.
Both round trips are definitionally the identity. -/
def reindexEquivalence (R : Cᵒᵖ ⥤ RingCat.{max u v}) :
    PresheafOfModules.{max u v} R ≌
      PresheafOfModules.{max u v} ((AsSmall.down : AsSmall.{0} C ⥤ C).op ⋙ R) where
  functor := PresheafOfModules.pushforward₀ AsSmall.down R
  inverse := PresheafOfModules.pushforward₀ AsSmall.up (AsSmall.down.op ⋙ R)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Raise objects and arrows to one common indexing universe using explicit lifts. -/
def reindexFunctor (F : C ⥤ D) : AsSmall.{0} C ⥤ AsSmall.{0} D :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

/-- The reindexed coefficient map consists of the original component maps. -/
def reindexCoefficients {F : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{max u v}}
    {R : Dᵒᵖ ⥤ RingCat.{max u v}} (φ : S ⟶ F.op ⋙ R) :
    (AsSmall.down : AsSmall.{0} C ⥤ C).op ⋙ S ⟶
      (reindexFunctor F).op ⋙ (AsSmall.down : AsSmall.{0} D ⥤ D).op ⋙ R :=
  Functor.whiskerLeft AsSmall.down.op φ

/-- Mathlib proves existence from free generators, coproducts and cokernels.
The coefficient and carrier universe is the size of the explicit small presentation. -/
theorem reindexPullback_exists {F : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{max u v}}
    {R : Dᵒᵖ ⥤ RingCat.{max u v}} (φ : S ⟶ F.op ⋙ R) :
    (PresheafOfModules.pushforward.{max u v} (reindexCoefficients φ)).IsRightAdjoint := by
  infer_instance

/-- Actual presheaf extension: reindex, apply the proved Mathlib pullback,
and reindex back. No admitted adjoint or universe-smallness witness is used. -/
def extendPresheaf {F : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{max u v}}
    {R : Dᵒᵖ ⥤ RingCat.{max u v}} (φ : S ⟶ F.op ⋙ R) :
    PresheafOfModules.{max u v} S ⥤ PresheafOfModules.{max u v} R := by
  -- Local instance justification (instance diamond): select the proved generator-based certificate for this explicit reindexed coefficient map.
  letI := reindexPullback_exists φ
  exact PresheafOfModules.pushforward₀ (AsSmall.down : AsSmall.{0} C ⥤ C) S ⋙
    PresheafOfModules.pullback (reindexCoefficients φ) ⋙
      PresheafOfModules.pushforward₀ (AsSmall.up : D ⥤ AsSmall.{0} D)
        ((AsSmall.down : AsSmall.{0} D ⥤ D).op ⋙ R)

/-- The explicit extension is genuinely left adjoint to the original
restriction functor, with the adjunction constructed from the specified pair. -/
def extendPresheafAdjunction {F : C ⥤ D} {S : Cᵒᵖ ⥤ RingCat.{max u v}}
    {R : Dᵒᵖ ⥤ RingCat.{max u v}} (φ : S ⟶ F.op ⋙ R) :
    extendPresheaf φ ⊣ PresheafOfModules.pushforward φ := by
  -- Local instance justification (instance diamond): the original-category adjunction uses the proved small-presentation pullback certificate.
  letI := reindexPullback_exists φ
  exact (((reindexEquivalence S).toAdjunction.comp
    (PresheafOfModules.pullbackPushforwardAdjunction (reindexCoefficients φ))).comp
      (reindexEquivalence R).symm.toAdjunction).ofNatIsoRight (Iso.refl _)

end Stacks1048Forward
