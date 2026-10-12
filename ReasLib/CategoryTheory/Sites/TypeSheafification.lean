/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Plus
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Mathlib.CategoryTheory.UnivLE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Presheaf.MonoEpi

/-!
# Type-valued sheafification

This file owns the universe-stable local properties of the `Type`-valued
`Plus` construction and sheafification unit. The large-universe weak
equivalence bridge is kept separately in `Sites.LargeTypeSheafification`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w w'

noncomputable section

namespace CategoryTheory.GrothendieckTopology

namespace TypeSheafification

/-- The plus presheaf associated to a Type-valued presheaf on a site. -/
def plusObj
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type w) [UnivLE.{max u v, w}] : Cᵒᵖ ⥤ Type w := J.plusObj P

/-- The canonical morphism from a Type-valued presheaf to its plus presheaf. -/
def toPlus
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type w) [UnivLE.{max u v, w}] : P ⟶ plusObj J P := J.toPlus P

/-- The double plus presheaf associated to a Type-valued presheaf is a sheaf. -/
theorem isSheaf_plus_plus
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type w) [UnivLE.{max u v, w}] :
    Presheaf.IsSheaf J (J.plusObj (J.plusObj P)) := by
  exact Plus.isSheaf_plus_plus J P

end TypeSheafification

/-- The plus construction of a Type-valued presheaf is separated. The universe-containment
hypothesis supplies the concrete colimits used by `plusObj`. -/
@[stacks 00WB "plus is separated"]
theorem plusObj_isSeparated
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type w) [UnivLE.{max u v, w}] :
    Presieve.IsSeparated J (J.plusObj P) := sorry

/-- The plus construction of a separated Type-valued presheaf is a sheaf. The universe
containment hypothesis is exactly what supplies the concrete colimits used by `plusObj`. -/
theorem plusObj_isSheaf_of_isSeparated
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type w) [UnivLE.{max u v, w}]
    (hP : Presieve.IsSeparated J P) :
    Presheaf.IsSheaf J (J.plusObj P) := sorry

/-- For a separated Type-valued presheaf, the canonical map to its plus construction is
injective on sections over every object. -/
@[stacks 00WB "plus unit injective"]
theorem toPlus_injective_of_isSeparated
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type w) [UnivLE.{max u v, w}]
    (hP : Presieve.IsSeparated J P) :
    ∀ U : C, Function.Injective ((J.toPlus P).app (op U)) := sorry

/-- For a separated Type-valued presheaf, the canonical map to its plus construction is a
monomorphism of presheaves. -/
@[stacks 00WB "plus unit mono"]
theorem toPlus_mono_of_isSeparated
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type w) [UnivLE.{max u v, w}]
    (hP : Presieve.IsSeparated J P) :
    Mono (J.toPlus P) := sorry

/-- The `Plus` map of a `Type`-valued presheaf is locally injective when the
concrete `Plus` construction is available. -/
theorem toPlus_isLocallyInjective_type
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, ∀ X : C, ∀ S : J.Cover X, HasMultiequalizer (S.index P)]
    [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (Type w))]
    (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective J (J.toPlus P) := sorry

/-- The `Plus` map of a `Type`-valued presheaf is locally surjective when the
concrete `Plus` construction is available. -/
theorem toPlus_isLocallySurjective_type
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, ∀ X : C, ∀ S : J.Cover X, HasMultiequalizer (S.index P)]
    [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget (Type w))]
    (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective J (J.toPlus P) := sorry

/-- Equality after the `Type`-valued sheafification unit forces the original
sections to agree locally when the type universe contains the site shapes. -/
theorem equalizerSieve_mem_of_toSheafify_eq_type_of_univLE
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] [UnivLE.{max u v, w}]
    {P : Cᵒᵖ ⥤ Type w} {X : Cᵒᵖ} (x y : P.obj X)
    (h : (toSheafify J P).app X x = (toSheafify J P).app X y) :
    Presheaf.equalizerSieve (F := P) x y ∈ J X.unop := sorry

/-- The `Type`-valued sheafification unit is locally injective in a universe
containing the site shapes. -/
theorem toSheafify_isLocallyInjective_type_of_univLE
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] [UnivLE.{max u v, w}]
    (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective J (toSheafify J P) := sorry

/-- For `Type`-valued presheaves, the unit of weak sheafification is locally
surjective without a universe-containment assumption. -/
theorem toSheafify_isLocallySurjective_type
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) := sorry

/-- The `Type`-valued sheafification unit is locally surjective in a universe
containing the site shapes. -/
theorem toSheafify_isLocallySurjective_type_of_univLE
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] [UnivLE.{max u v, w}] (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective J (toSheafify J P) := sorry

/-- In a type universe containing the site shapes, weak sheafification local
equivalences are exactly locally bijective morphisms. -/
theorem type_WEqualsLocallyBijective_of_univLE
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] [UnivLE.{max u v, w}] :
    J.WEqualsLocallyBijective (Type w) := sorry

/-- If all `Type`-valued sheafification units are locally injective, then weak
sheafification equivalences are exactly locally bijective maps.  Local
surjectivity of the units is supplied by
`toSheafify_isLocallySurjective_type`. -/
theorem type_WEqualsLocallyBijective_of_toSheafify_isLocallyInjective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)]
    (h_injective :
      ∀ P : Cᵒᵖ ⥤ Type w,
        Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P)) :
    J.WEqualsLocallyBijective (Type w) := sorry

/-- The `Plus` map is a weak sheafification equivalence in a type universe
containing the site shapes. -/
theorem toPlus_mem_W_of_univLE
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] [UnivLE.{max u v, w}]
    (P : Cᵒᵖ ⥤ Type w) :
    J.W (J.toPlus P) := sorry

/-- Whiskering a locally injective `Type`-valued presheaf map by `ULift`
preserves local injectivity. -/
theorem isLocallyInjective_whisker_ulift
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q) [Presheaf.IsLocallyInjective J f] :
    Presheaf.IsLocallyInjective J
      (Functor.whiskerRight f (uliftFunctor.{w', w} : Type w ⥤ Type (max w w'))) := sorry

/-- Whiskering a locally surjective `Type`-valued presheaf map by `ULift`
preserves local surjectivity. -/
theorem isLocallySurjective_whisker_ulift
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q) [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerRight f (uliftFunctor.{w', w} : Type w ⥤ Type (max w w'))) := sorry

/-- The identity functor on a universe of types preserves sheafification. -/
instance preservesSheafification_id_type
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    J.PreservesSheafification (𝟭 (Type w)) := sorry

/-- The concrete forgetful functor on a universe of types preserves
sheafification. -/
instance preservesSheafification_forget_type
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    J.PreservesSheafification (forget (Type w)) := sorry

/-- Two sections have the same sheafification image exactly when every map to
a `Type`-valued sheaf identifies them. -/
theorem toSheafify_app_eq_iff
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type w) [HasSheafify J (Type w)] [UnivLE.{max u v, w}] {X : Cᵒᵖ}
    (x y : P.obj X) :
    (toSheafify J P).app X x = (toSheafify J P).app X y ↔
      ∀ (Q : Sheaf J (Type w)) (f : P ⟶ Q.obj), f.app X x = f.app X y := sorry

/-!
## Representations by matching families

The declarations in this namespace describe the concrete two-stage `Plus`
model of `J.sheafify F`.  They deliberately retain the site-sized `Type
(max u v)` codomain of the construction, rather than adding universe
assumptions to source-facing representation statements.
-/

namespace Sheafify

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type (max u v))
variable (U : C)

/-- The image sieve of a sheafified section is covering, and every arrow in a
chosen cover carries a representative in the original presheaf. -/
lemma imageSieveCover
    (s : (J.sheafify F).obj (op U)) :
    ∃ (S : J.Cover U) (y : ∀ I : S.Arrow, F.obj (op I.Y)),
      ∀ I : S.Arrow,
        (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (y I) := sorry

/-- Local representatives of one sheafified section agree after a covering
refinement on every overlap. -/
lemma overlapEqualizerCover
    (s : (J.sheafify F).obj (op U))
    (S : J.Cover U)
    (y : ∀ I : S.Arrow, F.obj (op I.Y))
    (hy : ∀ I : S.Arrow,
      (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (y I)) :
    ∃ T : ∀ r : S.Relation, J.Cover r.r.Z,
      ∀ r : S.Relation, ∀ I : (T r).Arrow,
        F.map I.f.op (F.map r.r.g₁.op (y r.fst)) =
          F.map I.f.op (F.map r.r.g₂.op (y r.snd)) := sorry

/-- A section of `J.sheafify F` is represented by a matching family of
`F⁺`-sections over some cover. -/
lemma outerPlusRepresentation
    (s : (J.sheafify F).obj (op U)) :
    ∃ (S₀ : J.Cover U) (y : Meq (J.plusObj F) S₀),
      s = Plus.mk y := sorry

/-- Each local `F⁺`-section in an outer matching family is represented by a
matching family of `F`-sections over an inner cover. -/
lemma innerPlusRepresentatives
    {S₀ : J.Cover U} (y : Meq (J.plusObj F) S₀) :
    ∃ (T : ∀ I : S₀.Arrow, J.Cover I.Y)
      (t : ∀ I : S₀.Arrow, Meq F (T I)),
      ∀ I : S₀.Arrow, y I = Plus.mk (t I) := sorry

/-- Chosen inner representatives of compatible outer `F⁺`-sections admit a
common refinement on every outer overlap. -/
lemma overlapRefinement
    {S₀ : J.Cover U} (y : Meq (J.plusObj F) S₀)
    (T : ∀ I : S₀.Arrow, J.Cover I.Y)
    (t : ∀ I : S₀.Arrow, Meq F (T I))
    (ht : ∀ I : S₀.Arrow, y I = Plus.mk (t I)) :
    ∀ r : S₀.Relation,
      ∃ (W : J.Cover r.r.Z)
        (h₁ : W ⟶ (J.pullback r.r.g₁).obj (T r.fst))
        (h₂ : W ⟶ (J.pullback r.r.g₂).obj (T r.snd)),
        ((t r.fst).pullback r.r.g₁).refine h₁ = ((t r.snd).pullback r.r.g₂).refine h₂ := sorry

/-- A strict matching-family description of a sheafified section descends it
to a global `F⁺`-section. -/
lemma plusRepresentationOfStrictMatching
    (s : (J.sheafify F).obj (op U))
    {S : J.Cover U} (x : Meq F S)
    (hx : ∀ I : S.Arrow,
      (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (x I)) :
    ∃ y : (J.plusObj F).obj (op U),
      s = (J.toPlus (J.plusObj F)).app (op U) y := sorry

/-- Every section of `J.sheafify F` has a two-stage local representation by
matching families of sections of `F`. -/
theorem existsNestedPlusRepresentation
    (s : (J.sheafify F).obj (op U)) :
    ∃ (S₀ : J.Cover U) (y : Meq (J.plusObj F) S₀)
      (T : ∀ I : S₀.Arrow, J.Cover I.Y)
      (t : ∀ I : S₀.Arrow, Meq F (T I)),
      s = Plus.mk y ∧ ∀ I : S₀.Arrow, y I = Plus.mk (t I) := sorry

/-- A matching family of sections of `F` glues to a unique section of
`J.sheafify F` with the prescribed restrictions. -/
theorem existsUniqueSectionOfMatching
    (S : J.Cover U) (x : Meq F S) :
    ∃! s : (J.sheafify F).obj (op U),
      ∀ I : S.Arrow,
        (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (x I) := sorry

end Sheafify

end CategoryTheory.GrothendieckTopology
