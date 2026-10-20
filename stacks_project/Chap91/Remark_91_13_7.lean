module

public import stacks_project.Chap91.Lemma_91_13_4
public import stacks_project.Chap91.Lemma_91_13_6
public import stacks_project.Chap91.Remark_91_13_5
public import stacks_project.Chap91.Remark_91_13_7_Comparison
public import stacks_project.Chap91.Remark_91_13_7_Pullback
public import stacks_project.Chap91.Remark_91_13_7_Pushout
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Functoriality of square-zero f⁻¹O_B-algebra extensions by pushout and pullback

In the identity-base setting of Lemma 91.13.6, the pushout of
0 ⟶ F ⟶ O_{C'} ⟶ O_C ⟶ 0 along the adjunct of c : g^* F ⟶ G is a square-zero
g⁻¹ f⁻¹ O_B-algebra extension O'_1 of g⁻¹ O_C by G, and the pullback of
0 ⟶ G ⟶ O_{D'} ⟶ O_D ⟶ 0 along g^♯ is an extension O'_2. A fitting map g'
exists iff O'_1 ≅ O'_2 as such extensions, which are classified by the identified
Ext¹ groups Ext¹_{g⁻¹ O_C}(NL, G) = Ext¹_{O_D}(Lg^* NL, G).
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.FirstOrderThickening

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and Ext must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O_B O_C O_D : Sheaf J CommRingCat.{u}}
variable {fSharp : O_B ⟶ O_C} {gSharp : O_C ⟶ O_D}
variable {F : SheafOfModules (ringSheaf J O_C)}
variable {G : SheafOfModules (ringSheaf J O_D)}

namespace Solution

/- Remark 91.13.7 (1) Using pushout along the adjunct of c : g^* F ⟶ G we construct
an extension 0 ⟶ G ⟶ O'_1 ⟶ g⁻¹ O_C ⟶ 0 of square-zero g⁻¹ f⁻¹ O_B-algebras. -/
@[stacks 0GQ8] #check pushoutAlong

/- Remark 91.13.7 (2) Using pullback along g^♯ : g⁻¹ O_C ⟶ O_D we construct an
extension 0 ⟶ G ⟶ O'_2 ⟶ g⁻¹ O_C ⟶ 0 of square-zero g⁻¹ f⁻¹ O_B-algebras. -/
@[stacks 0GQ8] #check pullbackAlong

/-- Remark 91.13.7 (3) There exists a morphism g' of ringed topoi over
(Sh(B), O_B) compatible with g and c if and only if pushoutAlong c SC is
isomorphic to pullbackAlong SD as g⁻¹ f⁻¹ O_B-algebra extensions of
g⁻¹ O_C by G. -/
@[stacks 0GQ8]
theorem exists_fittingMap_iff_isoClass (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F))
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    Nonempty (FittingMap (RelativeDiagram.ofIdentityBase c SC SD)) ↔
      isoClassMk (pushoutAlong c SC) = isoClassMk (pullbackAlong SD) := sorry

/- Remark 91.13.7 (4) These extensions are classified by
Ext¹_{g⁻¹ O_C}(NL_{g⁻¹ O_C / g⁻¹ f⁻¹ O_B}, G) = Ext¹_{O_D}(Lg^* NL_{O_C / O_B}, G),
via tensor-hom adjunction and the two NL identifications. -/
@[stacks 0GQ8] #check extOne_restrictEquiv

/-- Remark 91.13.7 (5) The pushout extension O'_1 is the image of ξ under
Ext¹_{O_C}(NL_{O_C/O_B}, F) → Ext¹_{O_D}(Lg^* NL_{O_C/O_B}, G). -/
@[stacks 0GQ8]
theorem pushoutAlong_extClass (c : (extendAlong gSharp).obj F ⟶ G)
    (SC : Solution (𝟙 O_B) (isSquareZero_id O_B) fSharp F (zeroKernelMap fSharp F)) :
    extOne_restrictEquiv fSharp gSharp G
        ((extensionEquiv fSharp ((restrictionAlong gSharp).obj G)).symm
          (isoClassMk (pushoutAlong c SC))) =
      extOne_map c ((extensionEquiv fSharp F).symm (isoClassMk SC)) := sorry

/-- Remark 91.13.7 (6) The pullback extension O'_2 is the image of ζ under
Ext¹_{O_D}(NL_{O_D/O_B}, G) → Ext¹_{O_D}(Lg^* NL_{O_C/O_B}, G). -/
@[stacks 0GQ8]
theorem pullbackAlong_extClass
    (SD :
      Solution (𝟙 O_B) (isSquareZero_id O_B) (fSharp ≫ gSharp) G
        (zeroKernelMap (fSharp ≫ gSharp) G)) :
    extOne_restrictEquiv fSharp gSharp G
        ((extensionEquiv fSharp ((restrictionAlong gSharp).obj G)).symm
          (isoClassMk (pullbackAlong SD))) =
      extOne_comap fSharp gSharp
        ((extensionEquiv (fSharp ≫ gSharp) G).symm (isoClassMk SD)) := sorry

end Solution

end SheafOfModules.RingedSite.FirstOrderThickening

