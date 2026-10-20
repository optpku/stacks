/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.Infinitesimal

/-!
# First-order thickenings of a ringed topos

After identifying underlying topoi, a first-order thickening of a ringed topos `(Sh(C), O)`
is a locally surjective square-zero morphism `π : O' ⟶ O` of commutative ring sheaves on `C`.
Morphisms of such thickenings of a fixed `O` induce `O`-module maps of kernel ideals. Complexes and short exact sequences are defined
by these induced maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]

/-- A same-site first-order thickening of a commutative ring sheaf `O` is a locally surjective
square-zero morphism `π : O' ⟶ O`. -/
class IsFirstOrderThickening {O' O : Sheaf J CommRingCat.{max u v}} (π : O' ⟶ O) : Prop where
  [isLocallySurjective : Sheaf.IsLocallySurjective π]
  /-- The kernel ideal of `π` is square zero. -/
  isSquareZero : KernelIdeal.IsSquareZero π

attribute [instance] IsFirstOrderThickening.isLocallySurjective

/-- A morphism of commutative ring sheaves is a first-order thickening iff it is locally
surjective and its kernel ideal is square zero. -/
theorem isFirstOrderThickening_iff {O' O : Sheaf J CommRingCat.{max u v}} (π : O' ⟶ O) :
    IsFirstOrderThickening π ↔
      Sheaf.IsLocallySurjective π ∧ KernelIdeal.IsSquareZero π := sorry

/-- The identity morphism of a commutative ring sheaf is a first-order thickening. -/
instance instIsFirstOrderThickeningId (O : Sheaf J CommRingCat.{max u v}) :
    IsFirstOrderThickening (𝟙 O) where
  isSquareZero := sorry

namespace FirstOrderThickening

variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}] [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The kernel ideal of a first-order thickening, as an `O`-module. -/
noncomputable abbrev ideal {O' O : Sheaf J CommRingCat.{max u v}} (π : O' ⟶ O)
    [hπ : IsFirstOrderThickening π] :
    ringedSiteModuleCategory.{u, v, max u v, max u v} J O :=
  idealModule hπ.isSquareZero

/-- Forgetting the `O`-action on `ideal π` recovers the kernel ideal sheaf of `π`. -/
noncomputable abbrev ideal_forgetIso {O' O : Sheaf J CommRingCat.{max u v}} (π : O' ⟶ O)
    [hπ : IsFirstOrderThickening π] :
    (restrictionAlong π).obj (ideal π) ≅ KernelIdeal.sheaf π :=
  restrictIdealModuleIso hπ.isSquareZero

/-- A morphism of first-order thickenings of a fixed ring sheaf `O` is a morphism of the
thickened ring sheaves over `O`. -/
structure Hom {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}} (π₁ : O'₁ ⟶ O) (π₂ : O'₂ ⟶ O)
    [IsFirstOrderThickening π₁] [IsFirstOrderThickening π₂] where
  /-- The morphism of thickened ring sheaves `O'₂ ⟶ O'₁`. -/
  hom : O'₂ ⟶ O'₁
  /-- The morphism lies over `O`. -/
  comm : hom ≫ π₁ = π₂

/-- The identity morphism of a first-order thickening. -/
def Hom.id {O' O : Sheaf J CommRingCat.{max u v}} (π : O' ⟶ O) [IsFirstOrderThickening π] :
    Hom π π where
  hom := 𝟙 O'
  comm := Category.id_comp π

/-- Composition of morphisms of first-order thickenings of a fixed ring sheaf. -/
def Hom.comp {O'₁ O'₂ O'₃ O : Sheaf J CommRingCat.{max u v}} {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O}
    {π₃ : O'₃ ⟶ O} [IsFirstOrderThickening π₁] [IsFirstOrderThickening π₂]
    [IsFirstOrderThickening π₃] (f : Hom π₁ π₂) (g : Hom π₂ π₃) : Hom π₁ π₃ where
  hom := g.hom ≫ f.hom
  comm := sorry

/-- The additive map induced by a morphism over the base sends the source kernel ideal
into the kernel of the target projection. -/
theorem Hom.idealMap_kernel_condition {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} [IsFirstOrderThickening π₁]
    [IsFirstOrderThickening π₂] (f : Hom π₁ π₂) :
    ((SheafOfModules.toSheaf (ringSheaf J O'₂)).map (KernelIdeal.ι π₂) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap f.hom)) ≫
      (SheafOfModules.toSheaf (ringSheaf J O'₁)).map (KernelIdeal.map π₁) = 0 := sorry

/-- The underlying additive map between the descended kernel ideals induced by a morphism
of first-order thickenings. -/
noncomputable def Hom.idealMap_toSheaf {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} [hπ₁ : IsFirstOrderThickening π₁]
    [hπ₂ : IsFirstOrderThickening π₂] (f : Hom π₁ π₂) :
    (SheafOfModules.toSheaf (ringSheaf J O)).obj (ideal π₂) ⟶
      (SheafOfModules.toSheaf (ringSheaf J O)).obj (ideal π₁) :=
  (hπ₂.isSquareZero.targetModuleForgetIso (KernelIdeal.quotientComparison_isIso π₂)).hom ≫
    KernelIdeal.additiveLift π₁
      ((SheafOfModules.toSheaf (ringSheaf J O'₂)).map (KernelIdeal.ι π₂) ≫
        SheafOfModules.unitUnderlyingMap (ringSheafMap f.hom))
      (Hom.idealMap_kernel_condition f) ≫
    (hπ₁.isSquareZero.targetModuleForgetIso (KernelIdeal.quotientComparison_isIso π₁)).inv

/-- The induced additive map of descended kernel ideals is linear over the base ring sheaf. -/
theorem Hom.idealMap_smul {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} [IsFirstOrderThickening π₁]
    [IsFirstOrderThickening π₂] (f : Hom π₁ π₂) (U : Cᵒᵖ)
    (r : (ringSheaf J O).obj.obj U) (m : (ideal π₂).val.obj U) :
    f.idealMap_toSheaf.hom.app U (((ideal π₂).val.obj U).isModule.smul r m) =
      ((ideal π₁).val.obj U).isModule.smul r (f.idealMap_toSheaf.hom.app U m) := sorry

/-- A morphism of first-order thickenings induces a base-ring-linear map of kernel ideals. -/
noncomputable def Hom.idealMap {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} [IsFirstOrderThickening π₁]
    [IsFirstOrderThickening π₂] (f : Hom π₁ π₂) :
    ideal π₂ ⟶ ideal π₁ where
  val := PresheafOfModules.homMk f.idealMap_toSheaf.hom (Hom.idealMap_smul f)

/-- The identity morphism of a thickening induces the identity on kernel ideals. -/
theorem Hom.idealMap_id {O' O : Sheaf J CommRingCat.{max u v}} (π : O' ⟶ O)
    [IsFirstOrderThickening π] : (Hom.id π).idealMap = 𝟙 (ideal π) := sorry

/-- Kernel-ideal maps of composable morphisms of thickenings compose. -/
theorem Hom.idealMap_comp {O'₁ O'₂ O'₃ O : Sheaf J CommRingCat.{max u v}} {π₁ : O'₁ ⟶ O}
    {π₂ : O'₂ ⟶ O} {π₃ : O'₃ ⟶ O} [IsFirstOrderThickening π₁] [IsFirstOrderThickening π₂]
    [IsFirstOrderThickening π₃] (f : Hom π₁ π₂) (g : Hom π₂ π₃) :
    (Hom.comp f g).idealMap = g.idealMap ≫ f.idealMap := sorry

/-- A sequence of morphisms of first-order thickenings is a complex when the induced maps of
ideal sheaves compose to zero. -/
def IsComplex {O'₁ O'₂ O'₃ O : Sheaf J CommRingCat.{max u v}} {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O}
    {π₃ : O'₃ ⟶ O} [IsFirstOrderThickening π₁] [IsFirstOrderThickening π₂]
    [IsFirstOrderThickening π₃] (f : Hom π₁ π₂) (g : Hom π₂ π₃) : Prop :=
  g.idealMap ≫ f.idealMap = 0

/-- A sequence of morphisms of first-order thickenings is a complex iff the composite
`I₃ ⟶ I₂ ⟶ I₁` of induced kernel-ideal maps vanishes. -/
theorem isComplex_iff {O'₁ O'₂ O'₃ O : Sheaf J CommRingCat.{max u v}} {π₁ : O'₁ ⟶ O}
    {π₂ : O'₂ ⟶ O} {π₃ : O'₃ ⟶ O} [IsFirstOrderThickening π₁] [IsFirstOrderThickening π₂]
    [IsFirstOrderThickening π₃] (f : Hom π₁ π₂) (g : Hom π₂ π₃) :
    IsComplex f g ↔ g.idealMap ≫ f.idealMap = 0 := sorry

/-- A trivialization of a first-order thickening `π : O' ⟶ O` is a section of `π`. -/
def IsTrivialization {O' O : Sheaf J CommRingCat.{max u v}} (σ : O ⟶ O') (π : O' ⟶ O) : Prop :=
  σ ≫ π = 𝟙 O

/-- A morphism `σ : O ⟶ O'` trivializes `π` iff it satisfies the section equation
`σ ≫ π = 𝟙 O`. -/
theorem isTrivialization_iff {O' O : Sheaf J CommRingCat.{max u v}} (σ : O ⟶ O') (π : O' ⟶ O) :
    IsTrivialization σ π ↔ σ ≫ π = 𝟙 O := sorry

/-- If a sequence of morphisms of first-order thickenings is a complex, then the composite
`O'₃ ⟶ O'₁` factors uniquely through `π₃`, so `π₁` is a trivial first-order thickening with a
unique canonical trivialization. -/
theorem existsUnique_canonicalTrivialization {O'₁ O'₂ O'₃ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {π₃ : O'₃ ⟶ O} [IsFirstOrderThickening π₁]
    [IsFirstOrderThickening π₂] [IsFirstOrderThickening π₃] (f : Hom π₁ π₂)
    (g : Hom π₂ π₃) (h : IsComplex f g) :
    ∃! σ : O ⟶ O'₁, IsTrivialization σ π₁ ∧ g.hom ≫ f.hom = π₃ ≫ σ := sorry

/-- The two-term complex of kernel ideals induced by a complex of first-order thickenings. -/
noncomputable def idealShortComplex {O'₁ O'₂ O'₃ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {π₃ : O'₃ ⟶ O} [IsFirstOrderThickening π₁]
    [IsFirstOrderThickening π₂] [IsFirstOrderThickening π₃] (f : Hom π₁ π₂)
    (g : Hom π₂ π₃) (h : IsComplex f g) :
    ShortComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) :=
  ShortComplex.mk g.idealMap f.idealMap h

/-- A sequence of morphisms of first-order thickenings is short exact when the induced maps of
ideal sheaves form a short exact sequence of `O`-modules. -/
def IsShortExact {O'₁ O'₂ O'₃ O : Sheaf J CommRingCat.{max u v}} {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O}
    {π₃ : O'₃ ⟶ O} [IsFirstOrderThickening π₁] [IsFirstOrderThickening π₂]
    [IsFirstOrderThickening π₃] (f : Hom π₁ π₂) (g : Hom π₂ π₃) : Prop :=
  ∃ w : IsComplex f g, (idealShortComplex f g w).ShortExact

/-- Short exactness of a sequence of morphisms of first-order thickenings is short exactness of
the induced sequence of kernel ideals. -/
theorem isShortExact_iff {O'₁ O'₂ O'₃ O : Sheaf J CommRingCat.{max u v}} {π₁ : O'₁ ⟶ O}
    {π₂ : O'₂ ⟶ O} {π₃ : O'₃ ⟶ O} [IsFirstOrderThickening π₁] [IsFirstOrderThickening π₂]
    [IsFirstOrderThickening π₃] (f : Hom π₁ π₂) (g : Hom π₂ π₃) :
    IsShortExact f g ↔ ∃ w : IsComplex f g, (idealShortComplex f g w).ShortExact := sorry

/-- A short exact sequence of morphisms of first-order thickenings is a complex. -/
theorem isShortExact_isComplex {O'₁ O'₂ O'₃ O : Sheaf J CommRingCat.{max u v}} {π₁ : O'₁ ⟶ O}
    {π₂ : O'₂ ⟶ O} {π₃ : O'₃ ⟶ O} [IsFirstOrderThickening π₁] [IsFirstOrderThickening π₂]
    [IsFirstOrderThickening π₃] (f : Hom π₁ π₂) (g : Hom π₂ π₃) :
    IsShortExact f g → IsComplex f g := sorry

end FirstOrderThickening

end SheafOfModules.RingedSite
