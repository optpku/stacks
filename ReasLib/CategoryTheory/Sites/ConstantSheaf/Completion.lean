/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Flat
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.IdealPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic completion of a constant sheaf

For an ideal `I` of a commutative ring `R`, the completed constant sheaf is
the inverse limit of the constant quotient sheaves `R / I ^ n`.  This file
exposes both its `R`-module and commutative-ring realizations, the canonical
map from the constant ring sheaf, and the reduction modulo `I` comparison.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.ConstantSheaf

variable {C : Type u} [Category.{v} C]
variable {R : Type w} [CommRing R]

namespace AdicCompletion

namespace Module

variable (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]

/-- Lemma 18.42.4 (093M), module completion: the completed constant
`R`-module sheaf `lim n, (R / I ^ n)̲`. -/
@[stacks 093M "module completion"]
abbrev sheaf (I : Ideal R) : Sheaf J (ModuleCat.{w} R) :=
  limit (constantIdealPowerQuotientSheafSystem J I)

/-- Sections of the completed constant sheaf over `U`. -/
abbrev sections (I : Ideal R) (U : C) : ModuleCat.{w} R :=
  (sheaf J I).obj.obj (op U)

/-- Sections of the constant quotient sheaf `(R / I)̲` over `U`. -/
abbrev quotientSections (I : Ideal R) (U : C) : ModuleCat.{w} R :=
  (constantIdealQuotientSheaf J I).obj.obj (op U)

/-- The inverse system `n ↦ (R / I ^ n)̲(U)` of section modules. -/
abbrev sectionSystem (I : Ideal R) (U : C) :
    ℕᵒᵖ ⥤ ModuleCat.{w} R :=
  constantIdealPowerQuotientSheafSystem J I ⋙
    sheafToPresheaf J (ModuleCat.{w} R) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op U)

/-- Evaluation commutes with the inverse limit defining the completed
constant sheaf. -/
noncomputable def sectionsIsoLimit
    (I : Ideal R) (U : C) :
    sections J I U ≅ limit (sectionSystem J I U) :=
  preservesLimitIso
    (sheafToPresheaf J (ModuleCat.{w} R) ⋙
      (evaluation Cᵒᵖ (ModuleCat.{w} R)).obj (op U))
    (constantIdealPowerQuotientSheafSystem J I)

/-- Projection of completed sections onto the first nontrivial quotient
stage `(R / I)̲(U)`. -/
abbrev toQuotient (I : Ideal R) (U : C) :
    sections J I U ⟶ quotientSections J I U :=
  (limit.π (constantIdealPowerQuotientSheafSystem J I) (op 1)).hom.app (op U)

/-- The first quotient projection kills `I` times the completed section
module. -/
theorem smulTop_le_ker_toQuotient
    (I : Ideal R) (U : C) :
    I • (⊤ : Submodule R (sections J I U)) ≤
      LinearMap.ker (toQuotient J I U).hom := sorry

/-- Completed sections reduced modulo `I`, as a bundled `R`-module. -/
abbrev reduction (I : Ideal R) (U : C) : ModuleCat.{w} R :=
  ModuleCat.of R
    ((sections J I U) ⧸ (I • (⊤ : Submodule R (sections J I U))))

/-- The canonical comparison from completed sections modulo `I` to sections
of the constant quotient sheaf. -/
noncomputable def reductionComparison (I : Ideal R) (U : C) :
    reduction J I U ⟶ quotientSections J I U :=
  ModuleCat.ofHom <|
    (I • (⊤ : Submodule R (sections J I U))).liftQ
      (toQuotient J I U).hom (smulTop_le_ker_toQuotient J I U)

/-- The presheaf obtained by reducing the completed constant module sheaf
modulo `I` objectwise.  Restriction maps are the maps induced on module
quotients. -/
noncomputable def reductionPresheaf (I : Ideal R) : Cᵒᵖ ⥤ ModuleCat.{w} R where
  obj X := reduction J I X.unop
  map {X Y} f := ModuleCat.ofHom <|
    Submodule.mapQ
      (I • (⊤ : Submodule R (sections J I X.unop)))
      (I • (⊤ : Submodule R (sections J I Y.unop)))
      ((sheaf J I).obj.map f).hom
      (Submodule.smul_top_le_comap_smul_top I ((sheaf J I).obj.map f).hom)
  map_id := sorry
  map_comp := sorry

/-- Objectwise reduction modulo `I` of the completed constant module sheaf
is a sheaf. -/
theorem reductionPresheaf_isSheaf [IsNoetherianRing R] (I : Ideal R) :
    Presheaf.IsSheaf J (reductionPresheaf J I) := sorry

/-- The completed constant module sheaf reduced modulo `I`. -/
noncomputable abbrev reductionSheaf [IsNoetherianRing R] (I : Ideal R) :
    Sheaf J (ModuleCat.{w} R) :=
  ⟨reductionPresheaf J I, reductionPresheaf_isSheaf J I⟩

/-- The canonical natural comparison from the reduction of the completed
constant module sheaf to the constant quotient sheaf. -/
noncomputable def reductionComparisonNatTrans [IsNoetherianRing R]
    (I : Ideal R) :
    (reductionSheaf J I).obj ⟶ (constantIdealQuotientSheaf J I).obj where
  app X := reductionComparison J I X.unop
  naturality := sorry

/-- The canonical sheaf morphism from the completed constant module sheaf
modulo `I` to the constant sheaf with value `R / I`. -/
noncomputable def reductionSheafComparison [IsNoetherianRing R]
    (I : Ideal R) : reductionSheaf J I ⟶ constantIdealQuotientSheaf J I :=
  ObjectProperty.homMk (reductionComparisonNatTrans J I)

/-- Lemma 18.42.4 (093M) (1): for a Noetherian ring, the completed constant
module sheaf is sectionwise flat. -/
@[stacks 093M "(1)"]
theorem sectionwiseFlat
    [IsNoetherianRing R] (I : Ideal R) :
    (sheaf J I).SectionwiseFlat := sorry

/-- For a Noetherian ring, every section module of the completed constant
sheaf is flat. -/
theorem app_flat
    [IsNoetherianRing R] (I : Ideal R) (U : C) :
    Module.Flat R (sections J I U) := sorry

/-- The reduction comparison is an isomorphism of module sheaves. -/
noncomputable instance reductionSheafComparison_isIso
    [IsNoetherianRing R] (I : Ideal R) :
    IsIso (reductionSheafComparison J I) := sorry

/-- Lemma 18.42.4 (093M) (2): canonical identification of the completed
constant module sheaf modulo `I` with the constant sheaf on `R / I`. -/
@[stacks 093M "(2)"]
noncomputable def reductionSheafIso
    [IsNoetherianRing R] (I : Ideal R) :
    reductionSheaf J I ≅ constantIdealQuotientSheaf J I :=
  asIso (reductionSheafComparison J I)

/-- The canonical reduction isomorphism
`(lim n, (R / I ^ n)̲)(U) / I ≅ (R / I)̲(U)`. -/
noncomputable def reductionIso
    [IsNoetherianRing R] (I : Ideal R) (U : C) :
    reduction J I U ≅ quotientSections J I U :=
  ((sheafToPresheaf J (ModuleCat.{w} R)).mapIso
    (reductionSheafIso J I)).app (op U)

/-- The forward map of the reduction isomorphism is the canonical quotient
comparison. -/
@[simp]
theorem reductionIso_hom
    [IsNoetherianRing R] (I : Ideal R) (U : C) :
    (reductionIso J I U).hom = reductionComparison J I U := sorry

end Module

namespace Ideal

variable (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]

/-- Lemma 18.42.4 (093M), completed ideal: the sheaf
`lim n, (I / I ^ n)̲`. -/
@[stacks 093M "completed ideal"]
abbrev sheaf (I : Ideal R) : Sheaf J (ModuleCat.{w} R) :=
  limit (IdealPower.constantSubquotientSystem J I)

/-- The canonical morphism from the completed ideal sheaf to the completed
constant module sheaf, induced by `I / I ^ n ⟶ R / I ^ n` at every stage. -/
noncomputable def toCompletion (I : Ideal R) :
    sheaf J I ⟶ Module.sheaf J I :=
  lim.map (IdealPower.constantSubquotientToQuotient J I)

/-- The completed-ideal morphism commutes with every projection to an
ideal-power quotient stage. -/
theorem toCompletion_comp_π (I : Ideal R) (n : ℕᵒᵖ) :
    toCompletion J I ≫ limit.π (constantIdealPowerQuotientSheafSystem J I) n =
      limit.π (IdealPower.constantSubquotientSystem J I) n ≫
        (IdealPower.constantSubquotientToQuotient J I).app n := sorry

/-- Over a Noetherian ring, the completed ideal embeds in the completed
constant module sheaf. -/
noncomputable instance toCompletion_mono [IsNoetherianRing R] (I : Ideal R) :
    Mono (toCompletion J I) := sorry

/-- Objectwise, the image of the completed ideal is exactly `I` times the
completed constant module.  This is the reusable form of
`I R̂ = Ī`. -/
theorem range_app_eq_smulTop [IsNoetherianRing R] (I : Ideal R) (U : C) :
    LinearMap.range ((toCompletion J I).hom.app (op U)).hom =
      I • (⊤ : Submodule R (Module.sections J I U)) := sorry

end Ideal

namespace Ring

variable (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{w}]

/-- Lemma 18.42.4 (093M), adic algebra: the completed constant commutative
ring sheaf `lim n, (R / I ^ n)̲`. -/
@[stacks 093M "adic algebra"]
abbrev sheaf (I : Ideal R) : Sheaf J CommRingCat.{w} :=
  limit (constantIdealPowerQuotientRingSheafSystem J I)

/-- The cone from the constant ring sheaf `R̲` to its ideal-power quotient
tower.  Its components are the canonical quotient maps. -/
noncomputable def cone (I : Ideal R) :
    Cone (constantIdealPowerQuotientRingSheafSystem J I) where
  pt := (constantSheaf J CommRingCat.{w}).obj (CommRingCat.of R)
  π :=
    { app n := (constantSheaf J CommRingCat.{w}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n.unop)))
      naturality := sorry }

/-- The canonical morphism `R̲ ⟶ lim n, (R / I ^ n)̲` of commutative
ring sheaves. -/
noncomputable def map (I : Ideal R) :
    (constantSheaf J CommRingCat.{w}).obj (CommRingCat.of R) ⟶
      sheaf J I :=
  limit.lift (constantIdealPowerQuotientRingSheafSystem J I) (cone J I)

/-- The completion map followed by the `n`th projection is the canonical
quotient map `R̲ ⟶ (R / I ^ n)̲`. -/
theorem map_comp_π (I : Ideal R) (n : ℕᵒᵖ) :
    map J I ≫
        limit.π (constantIdealPowerQuotientRingSheafSystem J I) n =
      (cone J I).π.app n := sorry

end Ring

namespace Ring

section Flat

variable {S : Type max u v} [CommRing S]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]

/-- Lemma 18.42.4 (093M), flat-algebra form: the adic completion map is a flat
morphism of commutative ring sheaves; equivalently, the completed constant
ring sheaf is a flat algebra over the constant ring sheaf. -/
@[stacks 093M "flat algebra"]
theorem isFlat [IsNoetherianRing S] (I : Ideal S) :
    SheafOfModules.RingedSite.IsFlatHom (map J I) := sorry

end Flat

end Ring

end AdicCompletion

end CategoryTheory.ConstantSheaf
