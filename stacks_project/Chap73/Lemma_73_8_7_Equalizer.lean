/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Proper-surjective equalizer criteria on `(Spaces/X)`

This leaf records the equalizer presentation of a singleton proper-surjective
cover of algebraic spaces over `X` and the resulting sheaf criteria.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace
namespace Ph

/-- The type of sections on `V` equalized by the two projections of `V ×_U V`.

This is the canonical target for the restriction map associated with a
singleton cover `f : V ⟶ U`; it does not assume that `f` is proper or
surjective, allowing the construction to be reused for arbitrary arrows.
-/
def equalizer {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : (Over X)ᵒᵖ ⥤ Type v) {U V : Over X} (f : V ⟶ U) : Type v :=
  { s : F.obj (op V) //
      F.map (pullback.fst f f).op s = F.map (pullback.snd f f).op s }

/-- Restriction along `f` satisfies the two equalizer equations. -/
theorem equalizerMap_property {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : (Over X)ᵒᵖ ⥤ Type v) {U V : Over X} (f : V ⟶ U)
    (s : F.obj (op U)) :
    F.map (pullback.fst f f).op (F.map f.op s) =
      F.map (pullback.snd f f).op (F.map f.op s) :=
  sorry

/-- The canonical restriction map into the equalizer associated with `f`. -/
def equalizerMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : (Over X)ᵒᵖ ⥤ Type v) {U V : Over X} (f : V ⟶ U) :
    F.obj (op U) → equalizer F f :=
  fun s ↦ ⟨F.map f.op s, equalizerMap_property F f s⟩

/-- The underlying section of `equalizerMap F f s` is the restriction of `s`
along `f`. -/
@[simp]
theorem equalizerMap_val {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : (Over X)ᵒᵖ ⥤ Type v) {U V : Over X} (f : V ⟶ U)
    (s : F.obj (op U)) :
    (equalizerMap F f s).val = F.map f.op s :=
  sorry

namespace Sheaf

/-- A presheaf satisfies the singleton proper-surjective sheaf condition. -/
def IsProperSurjective {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : (Over X)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃U V : Over X⦄ (f : V ⟶ U) [Proper f.left] [Surjective f.left],
    Presieve.IsSheafFor F (Presieve.singleton f)

/-- The singleton presieve sheaf condition is equivalent to bijectivity of the
canonical map into `equalizer F f`. -/
theorem singleton_iff_bijective {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : (Over X)ᵒᵖ ⥤ Type v) {U V : Over X} (f : V ⟶ U) :
    Presieve.IsSheafFor F (Presieve.singleton f) ↔
      Function.Bijective (equalizerMap F f) :=
  sorry

end Sheaf

namespace Equalizer

/-- A presheaf satisfies the proper-surjective equalizer condition. -/
def IsProperSurjective {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : (Over X)ᵒᵖ ⥤ Type v) : Prop :=
  ∀ ⦃U V : Over X⦄ (f : V ⟶ U) [Proper f.left] [Surjective f.left],
    Function.Bijective (equalizerMap F f)

/-- The proper-surjective equalizer condition is equivalent to the singleton
sheaf condition. -/
theorem iffSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : (Over X)ᵒᵖ ⥤ Type v) :
    IsProperSurjective F ↔ Sheaf.IsProperSurjective F :=
  sorry

end Equalizer

end Ph
end AlgebraicGeometry.AlgebraicSpace
