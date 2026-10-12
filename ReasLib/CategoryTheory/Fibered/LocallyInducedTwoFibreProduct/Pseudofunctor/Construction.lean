/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Coherence.Composition
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Map.Functor
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudofunctor construction for locally induced two-fibre products

The construction is the composite of the canonical cospan map and explicit pseudo-pullback
pseudofunctor, followed by the generic full-subbicategory and locally induced lifts. Only the
two membership bridges are specific to selected two-fibre products; all pseudofunctor coherence
is inherited from reusable owners.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced
namespace TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [closed : BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable [projections : Projections.Has (P := P) (Q := Q)]
variable [isoClosed : Q.IsClosedUnderIsomorphisms]
variable [detected : Projections.IsDetected (P := P) (Q := Q)]

namespace pseudofunctor

/-- The ambient explicit pseudo-pullback pseudofunctor after forgetting selected morphisms and
object witnesses from the source cospans. -/
noncomputable def ambientBase :
    Bicategory.Cospan
        (Bicategory.LocallyInducedBicategory
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q) ⥤ᵖ
      BasedCategory.{max v vB, max w (max u (max v vB))} C :=
  (Bicategory.Cospan.map
      (Bicategory.LocallyInducedBicategory.forget
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor).comp
    (BasedCategory.PseudoPullback.pseudofunctor C)

omit projections isoClosed detected in
include closed in
/-- Relative pseudo-pullback closure puts every object of the ambient construction back in the
selected full subbicategory. -/
theorem ambientBase.obj_mem
    (S : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)) :
    P ((ambientBase (P := P) (Q := Q)).obj S) := sorry

/-- The ambient pseudofunctor with the selected object property restored by the generic
full-subbicategory lift. -/
noncomputable def ambient :
    Bicategory.Cospan
        (Bicategory.LocallyInducedBicategory
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q) ⥤ᵖ
      P.FullSubbicategory :=
  ObjectProperty.FullSubbicategory.liftPseudofunctor
    (ambientBase (P := P) (Q := Q))
    (ambientBase.obj_mem (P := P) (Q := Q))

include projections isoClosed detected in
/-- Projection detection puts every mapped cospan morphism back in the selected hom property. -/
theorem ambient.map_mem
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    Q ((ambient (P := P) (Q := Q)).obj S)
      ((ambient (P := P) (Q := Q)).obj T)
      ((ambient (P := P) (Q := Q)).map ψ).hom := sorry

end pseudofunctor

variable (P Q) in
/-- The explicit locally induced two-fibre-product construction as a pseudofunctor on bundled
selected cospans.

This is the generic locally induced lift of the generic full-subbicategory lift of the ordinary
explicit pseudo-pullback pseudofunctor. Its non-`Prop` object, map, `2`-cell, and comparison data
therefore come from the neutral cospan and pseudo-pullback owners; relative closure and projection
detection supply only the two membership witnesses. -/
@[stacks 02XQ "locally induced two-fibre-product pseudofunctor"]
noncomputable def pseudofunctor :
    Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) ⥤ᵖ
      Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q :=
  Bicategory.LocallyInducedBicategory.liftPseudofunctor
    (pseudofunctor.ambient (P := P) (Q := Q))
    (pseudofunctor.ambient.map_mem (P := P) (Q := Q))

/-- The object action of the locally induced two-fibre-product pseudofunctor is the explicit
selected apex. -/
@[simp]
theorem pseudofunctor.obj
    (S : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)) :
    (pseudofunctor P Q).obj S = apex S.fst S.snd := sorry

/-- The `1`-cell action of the locally induced two-fibre-product pseudofunctor is the existing
componentwise selected map. -/
@[simp]
theorem pseudofunctor.map
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : S ⟶ T) :
    (pseudofunctor P Q).map ψ =
      map (Bicategory.Cospan.Hom.toCospanTransform ψ) := sorry

/-- The `2`-cell action of the locally induced two-fibre-product pseudofunctor is the existing
locally full transformation. -/
@[simp]
theorem pseudofunctor.map₂
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    {ψ φ : S ⟶ T} (Γ : ψ ⟶ φ) :
    (pseudofunctor P Q).map₂ Γ =
      map₂ (Bicategory.Cospan.Hom₂.toModification Γ) := sorry

/-- The identity comparison of the locally induced two-fibre-product pseudofunctor is the
existing explicit identity comparison. -/
@[simp]
theorem pseudofunctor.mapId
    (S : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)) :
    (pseudofunctor P Q).mapId S = map.idIso S.fst S.snd := sorry

/-- The composition comparison of the locally induced two-fibre-product pseudofunctor is the
existing explicit composition comparison. -/
@[simp]
theorem pseudofunctor.mapComp
    {R S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    (pseudofunctor P Q).mapComp ψ φ =
      map.compIso
        (Bicategory.Cospan.Hom.toCospanTransform ψ)
        (Bicategory.Cospan.Hom.toCospanTransform φ) := sorry

/-- On each hom category, the locally induced two-fibre-product pseudofunctor is the
computational hom functor after exposing bundled cospan transformations. -/
@[simp]
theorem pseudofunctor.mapFunctor
    (S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)) :
    (pseudofunctor P Q).mapFunctor S T =
      (Bicategory.Cospan.inclusion
        (B := Bicategory.LocallyInducedBicategory
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q)).mapFunctor S T ⋙
        mapFunctor (F₁ := S.fst) (G₁ := S.snd)
          (F₂ := T.fst) (G₂ := T.snd) := sorry

end TwoFibreProduct
end LocallyInduced

end CategoryTheory
