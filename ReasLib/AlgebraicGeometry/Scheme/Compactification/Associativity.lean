/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Composition
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Triple compactifications for derived étale lower shriek associativity

A compatible tower `(P_h, P_g, P_bar)` of compactifications for separated
finite-type morphisms `f : X ⟶ Y`, `g : Y ⟶ Z`, and `h : Z ⟶ T` of qcqs
schemes, together with the interiors `W ⊂ Ȳ` and `U ⊂ V ⊂ X̄` for
a triple composite, inducing four composition diagrams.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace etaleDerivedLowerShriek

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsSeparated g] [Scheme.Hom.FiniteType g]
variable [IsSeparated h] [Scheme.Hom.FiniteType h]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace Z] [QuasiSeparatedSpace Z]
variable [CompactSpace T] [QuasiSeparatedSpace T]

/-- A compactification of `h : Z ⟶ T`, then of `g` over that ambient, then of
`X` over the resulting ambient, as in the construction of the associativity
square of `Rf_! ⋙ Rg_! ⋙ Rh_! ⟶ R(h ∘ g ∘ f)_!`. -/
structure AssocDiagram where
  /-- Compactification of `h : Z ⟶ T`. -/
  P_h : Of T (Over.mk h)
  /-- Compactification of `Y` over the ambient of `P_h`. -/
  P_g : Of P_h.obj.right.left (Over.mk (g ≫ Of.ι P_h))
  /-- Compactification of `X` over the ambient of `P_g`. -/
  P_bar : Of P_g.obj.right.left (Over.mk (X.hom ≫ Of.ι P_g))

namespace AssocDiagram

/-- Package three compatible compactifications as an associativity diagram. -/
def of (P_h : Of T (Over.mk h))
    (P_g : Of P_h.obj.right.left (Over.mk (g ≫ Of.ι P_h)))
    (P_bar : Of P_g.obj.right.left (Over.mk (X.hom ≫ Of.ι P_g))) :
    AssocDiagram X g h where
  P_h := P_h
  P_g := P_g
  P_bar := P_bar

variable (A : AssocDiagram X g h)

/-- The composition diagram for `g` then `h`, giving `γ_C`. -/
def compHG : CompDiagram (Over.mk g) h :=
  CompDiagram.of (Over.mk g) h A.P_h A.P_g

/-- The inverse image `W ⊂ Ȳ` of `Z` under `Ȳ ⟶ Z̄`. -/
def baseInterior : Scheme.{u} :=
  CompDiagram.interior (Over.mk g) h (compHG X g h A)

/-- Unfolding recovers the interior of `compHG`. -/
theorem baseInterior_eq :
    baseInterior X g h A = CompDiagram.interior (Over.mk g) h (compHG X g h A) :=
  rfl

/-- The open immersion `W ⟶ Ȳ`, base change of the interior of `P_h`. -/
def openBase : baseInterior X g h A ⟶ A.P_g.obj.right.left :=
  CompDiagram.openImmersion (Over.mk g) h (compHG X g h A)

/-- Unfolding recovers the open immersion of `compHG`. -/
theorem openBase_eq :
    openBase X g h A = CompDiagram.openImmersion (Over.mk g) h (compHG X g h A) :=
  rfl

/-- The inverse image `V ⊂ X̄` of `W` under `X̄ ⟶ Ȳ`. -/
def midInterior : Scheme.{u} :=
  pullback (openBase X g h A) A.P_bar.obj.right.hom

/-- The structure map `V ⟶ W`. -/
def toMidBase : midInterior X g h A ⟶ baseInterior X g h A :=
  pullback.fst (openBase X g h A) A.P_bar.obj.right.hom

/-- The open immersion `V ⟶ X̄`. -/
def openMid : midInterior X g h A ⟶ A.P_bar.obj.right.left :=
  pullback.snd (openBase X g h A) A.P_bar.obj.right.hom

/-- The compactification triangle of `P_bar` after composing with `Y ⟶ W`. -/
theorem ιMid_fac :
    (X.hom ≫ CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h (compHG X g h A)) ≫
        openBase X g h A =
      Of.ι A.P_bar ≫ A.P_bar.obj.right.hom :=
  (Category.assoc X.hom
      (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h (compHG X g h A))
      (openBase X g h A)).trans
    ((congrArg (fun t ↦ X.hom ≫ t)
        (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
          (compHG X g h A))).trans
      (Over.w A.P_bar.obj.hom).symm)

/-- The interior map `X ⟶ V` induced by the compactification of `X` over `Ȳ`. -/
def ιMid : X.left ⟶ midInterior X g h A :=
  pullback.lift
    (X.hom ≫ CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h (compHG X g h A))
    (Of.ι A.P_bar) (ιMid_fac X g h A)

/-- The triangle `X ⟶ V ⟶ W` recovers `X ⟶ Y ⟶ W`. -/
theorem ιMid_comp_toMidBase :
    ιMid X g h A ≫ toMidBase X g h A =
      X.hom ≫ CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h (compHG X g h A) :=
  pullback.lift_fst
    (X.hom ≫ CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h (compHG X g h A))
    (Of.ι A.P_bar) (ιMid_fac X g h A)

/-- The triangle `X ⟶ V ⟶ X̄` recovers the interior of `P_bar`. -/
theorem ιMid_comp_openMid :
    ιMid X g h A ≫ openMid X g h A = Of.ι A.P_bar :=
  pullback.lift_snd
    (X.hom ≫ CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h (compHG X g h A))
    (Of.ι A.P_bar) (ιMid_fac X g h A)

/-- The induced map `X ⟶ V` is an open immersion. -/
theorem isOpenImmersion_ιMid : IsOpenImmersion (ιMid X g h A) :=
  sorry

/-- The induced map `X ⟶ V` is quasi-compact. -/
theorem quasiCompact_ιMid : QuasiCompact (ιMid X g h A) :=
  sorry

/-- The map `V ⟶ W` is proper, as a base change of the proper ambient map of
`P_bar`. -/
theorem isProper_toMidBase : IsProper (toMidBase X g h A) :=
  sorry

/-- Compactification of `X` over `W` with ambient `V` and interior `X ⟶ V`. -/
def ofMid :
    Of (baseInterior X g h A)
      (Over.mk (X.hom ≫ CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h (compHG X g h A))) :=
  @Of.mk (baseInterior X g h A)
    (Over.mk (X.hom ≫ CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h (compHG X g h A)))
    (Over.mk (toMidBase X g h A))
    (Over.homMk (ιMid X g h A) (ιMid_comp_toMidBase X g h A))
    (isOpenImmersion_ιMid X g h A) (quasiCompact_ιMid X g h A)
    (isProper_toMidBase X g h A)

/-- The interior of `ofMid` is `X ⟶ V`. -/
theorem ofMid_ι : Of.ι (ofMid X g h A) = ιMid X g h A :=
  rfl

/-- The structure map of `ofMid` is `V ⟶ W`. -/
theorem ofMid_hom : (ofMid X g h A).obj.right.hom = toMidBase X g h A :=
  rfl

/-- The composition diagram for `f` then `g`, giving `γ_A`. -/
def compFG : CompDiagram X g :=
  CompDiagram.of X g
    (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h (compHG X g h A)) (ofMid X g h A)

/-- The ambient of the compactification of `g ∘ h` is `Ȳ` over `T`. -/
theorem compositeBase_fac :
    Of.ι A.P_g ≫ (A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom) = g ≫ h :=
  (Category.assoc (Of.ι A.P_g) A.P_g.obj.right.hom A.P_h.obj.right.hom).symm.trans
    ((congrArg (fun t ↦ t ≫ A.P_h.obj.right.hom) (Over.w A.P_g.obj.hom)).trans
      ((Category.assoc g (Of.ι A.P_h) A.P_h.obj.right.hom).trans
        (congrArg (fun t ↦ g ≫ t) (Over.w A.P_h.obj.hom))))

/-- The composite ambient morphism `Ȳ ⟶ T` is proper. -/
theorem isProper_P_g_comp_P_h :
    IsProper (A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom) :=
  sorry

/-- Compactification of `g ≫ h : Y ⟶ T` with ambient `Ȳ` and interior
`Of.ι P_g`. -/
def compositeBase : Of T (Over.mk (g ≫ h)) :=
  @Of.mk T (Over.mk (g ≫ h))
    (Over.mk (A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom))
    (Over.homMk (Of.ι A.P_g) (compositeBase_fac X g h A))
    (Of.instIsOpenImmersion _ _ A.P_g) A.P_g.property.quasiCompact
    (isProper_P_g_comp_P_h X g h A)

/-- The interior of `compositeBase` is the interior of `P_g`. -/
theorem compositeBase_ι : Of.ι (compositeBase X g h A) = Of.ι A.P_g :=
  rfl

/-- The structure map of `compositeBase` is `Ȳ ⟶ T`. -/
theorem compositeBase_hom :
    (compositeBase X g h A).obj.right.hom =
      A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom :=
  rfl

/-- The composition diagram for `f` then `h ∘ g`, giving
`γ_{A+B}`. -/
def compF : CompDiagram X (g ≫ h) :=
  CompDiagram.of X (g ≫ h) (compositeBase X g h A) A.P_bar

/-- The inverse image `U ⊂ X̄` of `Y` under `X̄ ⟶ Ȳ`. -/
def interior : Scheme.{u} :=
  CompDiagram.interior X (g ≫ h) (compF X g h A)

/-- Unfolding recovers the interior of `compF`. -/
theorem interior_eq :
    interior X g h A = CompDiagram.interior X (g ≫ h) (compF X g h A) :=
  rfl

/-- The ambient of the compactification of `g ∘ f` over `Z̄` is `X̄`. -/
theorem compositeOverBase_fac :
    Of.ι A.P_bar ≫ (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom) =
      (X.hom ≫ g) ≫ Of.ι A.P_h :=
  (Category.assoc (Of.ι A.P_bar) A.P_bar.obj.right.hom
      A.P_g.obj.right.hom).symm.trans
    ((congrArg (fun t ↦ t ≫ A.P_g.obj.right.hom) (Over.w A.P_bar.obj.hom)).trans
      ((Category.assoc X.hom (Of.ι A.P_g) A.P_g.obj.right.hom).trans
        ((congrArg (fun t ↦ X.hom ≫ t) (Over.w A.P_g.obj.hom)).trans
          (Category.assoc X.hom g (Of.ι A.P_h)).symm)))

/-- The composite ambient morphism `X̄ ⟶ Z̄` is proper. -/
theorem isProper_P_bar_comp_P_g :
    IsProper (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom) :=
  sorry

/-- Compactification of `X` over `Z̄` with ambient `X̄` and interior
`Of.ι P_bar`. -/
def compositeOverBase :
    Of A.P_h.obj.right.left (Over.mk ((X.hom ≫ g) ≫ Of.ι A.P_h)) :=
  @Of.mk A.P_h.obj.right.left (Over.mk ((X.hom ≫ g) ≫ Of.ι A.P_h))
    (Over.mk (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom))
    (Over.homMk (Of.ι A.P_bar) (compositeOverBase_fac X g h A))
    (Of.instIsOpenImmersion _ _ A.P_bar) A.P_bar.property.quasiCompact
    (isProper_P_bar_comp_P_g X g h A)

/-- The interior of `compositeOverBase` is the interior of `P_bar`. -/
theorem compositeOverBase_ι :
    Of.ι (compositeOverBase X g h A) = Of.ι A.P_bar :=
  rfl

/-- The structure map of `compositeOverBase` is `X̄ ⟶ Z̄`. -/
theorem compositeOverBase_hom :
    (compositeOverBase X g h A).obj.right.hom =
      A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom :=
  rfl

/-- The composition diagram for `g ∘ f` then `h`, giving
`γ_{B+C}`. -/
def compH : CompDiagram (Over.mk (X.hom ≫ g)) h :=
  CompDiagram.of (Over.mk (X.hom ≫ g)) h A.P_h (compositeOverBase X g h A)

/-- Commutativity witness for the pasting map `V ⟶ X̄ ×_{Z̄} Z`. -/
theorem midPasting_fac :
    (toMidBase X g h A ≫
          CompDiagram.toBase (Over.mk g) h (compHG X g h A)) ≫
        Of.ι A.P_h =
      openMid X g h A ≫ (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom) :=
  (Category.assoc (toMidBase X g h A)
      (CompDiagram.toBase (Over.mk g) h (compHG X g h A)) (Of.ι A.P_h)).trans
    ((congrArg (fun t ↦ toMidBase X g h A ≫ t)
        (pullback.condition :
          CompDiagram.toBase (Over.mk g) h (compHG X g h A) ≫ Of.ι A.P_h =
            CompDiagram.openImmersion (Over.mk g) h (compHG X g h A) ≫
              A.P_g.obj.right.hom)).trans
      ((Category.assoc (toMidBase X g h A) (openBase X g h A)
          A.P_g.obj.right.hom).symm.trans
        ((congrArg (fun t ↦ t ≫ A.P_g.obj.right.hom)
            (pullback.condition :
              toMidBase X g h A ≫ openBase X g h A =
                openMid X g h A ≫ A.P_bar.obj.right.hom)).trans
          (Category.assoc (openMid X g h A) A.P_bar.obj.right.hom
            A.P_g.obj.right.hom))))

/-- The pasting map `V ⟶ X̄ ×_{Z̄} Z` identifying the two models of the
inverse image of `Z` in `X̄`. -/
def midPasting : midInterior X g h A ⟶
    CompDiagram.interior (Over.mk (X.hom ≫ g)) h (compH X g h A) :=
  pullback.lift
    (toMidBase X g h A ≫ CompDiagram.toBase (Over.mk g) h (compHG X g h A))
    (openMid X g h A) (midPasting_fac X g h A)

/-- The pasting map lies over `Z`. -/
theorem midPasting_toBase :
    midPasting X g h A ≫
        CompDiagram.toBase (Over.mk (X.hom ≫ g)) h (compH X g h A) =
      toMidBase X g h A ≫ CompDiagram.toBase (Over.mk g) h (compHG X g h A) :=
  pullback.lift_fst
    (toMidBase X g h A ≫ CompDiagram.toBase (Over.mk g) h (compHG X g h A))
    (openMid X g h A) (midPasting_fac X g h A)

/-- The pasting map composes to the open immersion `V ⟶ X̄`. -/
theorem midPasting_open :
    midPasting X g h A ≫
        CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h (compH X g h A) =
      openMid X g h A :=
  pullback.lift_snd
    (toMidBase X g h A ≫ CompDiagram.toBase (Over.mk g) h (compHG X g h A))
    (openMid X g h A) (midPasting_fac X g h A)

/-- The ambient map of `ofComposite` of `compFG` is `V ⟶ Z`. -/
theorem ofCompositeFG_hom :
    (CompDiagram.ofComposite X g (compFG X g h A)).obj.right.hom =
      toMidBase X g h A ≫ CompDiagram.toBase (Over.mk g) h (compHG X g h A) :=
  rfl

/-- The pasting map is a morphism over `Z`. -/
theorem midPasting_over :
    midPasting X g h A ≫
        CompDiagram.toBase (Over.mk (X.hom ≫ g)) h (compH X g h A) =
      (CompDiagram.ofComposite X g (compFG X g h A)).obj.right.hom :=
  (midPasting_toBase X g h A).trans (ofCompositeFG_hom X g h A).symm

/-- The source of `ofComposite` of `compFG` is the mid-interior `V`. -/
theorem ofCompositeFG_left :
    (CompDiagram.ofComposite X g (compFG X g h A)).obj.right.left =
      midInterior X g h A :=
  rfl

/-- The source of `ofInterior` of `compH` is the interior of `compH`. -/
theorem ofInteriorH_left :
    (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h (compH X g h A)).obj.right.left =
      CompDiagram.interior (Over.mk (X.hom ≫ g)) h (compH X g h A) :=
  rfl

/-- Commutativity of interiors along the pasting map. -/
theorem midPasting_ι :
    (CompDiagram.ofComposite X g (compFG X g h A)).obj.hom ≫
        Over.homMk
          (eqToHom (ofCompositeFG_left X g h A) ≫
            midPasting X g h A ≫ eqToHom (ofInteriorH_left X g h A).symm)
          (midPasting_over X g h A) =
      (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h (compH X g h A)).obj.hom :=
  sorry

/-- Compactification morphism from the `γ_A` composite model of `g ∘ f` to the
interior model of `γ_{B+C}`. -/
def ofCompositeFG_hom_ofInteriorH :
    CompDiagram.ofComposite X g (compFG X g h A) ⟶
      CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h (compH X g h A) :=
  InducedCategory.homMk
    (Under.homMk
      (Over.homMk
        (eqToHom (ofCompositeFG_left X g h A) ≫
          midPasting X g h A ≫ eqToHom (ofInteriorH_left X g h A).symm)
        (midPasting_over X g h A))
      (midPasting_ι X g h A))

/-- Commutativity witness for the inverse pasting `X̄ ×_{Z̄} Z ⟶ W`. -/
theorem toBaseInterior_fac :
    CompDiagram.toBase (Over.mk (X.hom ≫ g)) h (compH X g h A) ≫ Of.ι A.P_h =
      (CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h (compH X g h A) ≫
          A.P_bar.obj.right.hom) ≫
        A.P_g.obj.right.hom :=
  (pullback.condition :
      CompDiagram.toBase (Over.mk (X.hom ≫ g)) h (compH X g h A) ≫ Of.ι A.P_h =
        CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h (compH X g h A) ≫
          (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom)).trans
    (Category.assoc
      (CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h (compH X g h A))
      A.P_bar.obj.right.hom A.P_g.obj.right.hom).symm

/-- The map `X̄ ×_{Z̄} Z ⟶ W` from the inverse-image pasting. -/
def toBaseInterior :
    CompDiagram.interior (Over.mk (X.hom ≫ g)) h (compH X g h A) ⟶
      baseInterior X g h A :=
  pullback.lift
    (CompDiagram.toBase (Over.mk (X.hom ≫ g)) h (compH X g h A))
    (CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h (compH X g h A) ≫
      A.P_bar.obj.right.hom)
    (toBaseInterior_fac X g h A)

/-- Commutativity witness for the inverse pasting `X̄ ×_{Z̄} Z ⟶ V`. -/
theorem midPastingInv_fac :
    toBaseInterior X g h A ≫ openBase X g h A =
      CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h (compH X g h A) ≫
        A.P_bar.obj.right.hom :=
  pullback.lift_snd
    (CompDiagram.toBase (Over.mk (X.hom ≫ g)) h (compH X g h A))
    (CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h (compH X g h A) ≫
      A.P_bar.obj.right.hom)
    (toBaseInterior_fac X g h A)

/-- The inverse pasting map `X̄ ×_{Z̄} Z ⟶ V`. -/
def midPastingInv :
    CompDiagram.interior (Over.mk (X.hom ≫ g)) h (compH X g h A) ⟶
      midInterior X g h A :=
  pullback.lift (toBaseInterior X g h A)
    (CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h (compH X g h A))
    (midPastingInv_fac X g h A)

/-- The inverse pasting map lies over `Z`. -/
theorem midPastingInv_over :
    midPastingInv X g h A ≫
        (CompDiagram.ofComposite X g (compFG X g h A)).obj.right.hom =
      CompDiagram.toBase (Over.mk (X.hom ≫ g)) h (compH X g h A) :=
  sorry

/-- Commutativity of interiors along the inverse pasting map. -/
theorem midPastingInv_ι :
    (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h (compH X g h A)).obj.hom ≫
        Over.homMk
          (eqToHom (ofInteriorH_left X g h A) ≫
            midPastingInv X g h A ≫ eqToHom (ofCompositeFG_left X g h A).symm)
          (midPastingInv_over X g h A) =
      (CompDiagram.ofComposite X g (compFG X g h A)).obj.hom :=
  sorry

/-- Compactification morphism from the interior model of `γ_{B+C}` to the `γ_A`
composite model of `g ∘ f`. -/
def ofInteriorH_hom_ofCompositeFG :
    CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h (compH X g h A) ⟶
      CompDiagram.ofComposite X g (compFG X g h A) :=
  InducedCategory.homMk
    (Under.homMk
      (Over.homMk
        (eqToHom (ofInteriorH_left X g h A) ≫
          midPastingInv X g h A ≫ eqToHom (ofCompositeFG_left X g h A).symm)
        (midPastingInv_over X g h A))
      (midPastingInv_ι X g h A))

end AssocDiagram

end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale

end

/-! Pullback-pasting identification of the first interiors. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram

/-- Equality transport of a pullback cospan preserves its first projection. -/
private theorem pullbackCongrHom_first {C : Type*} [Category C] {P Q R : C}
    {f₁ f₂ : P ⟶ R} {g₁ g₂ : Q ⟶ R} [HasPullback f₁ g₁] [HasPullback f₂ g₂]
    (hf : f₁ = f₂) (hg : g₁ = g₂) :
    (pullback.congrHom hf hg).hom ≫ pullback.fst f₂ g₂ = pullback.fst f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom, pullback.map]

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T]
  (A : AssocDiagram X g h)

/-- The two choices of the interior of f are related by actual pullback pasting. -/
def firstInteriorIso : CompDiagram.interior X g A.compFG ≅
    CompDiagram.interior X (g ≫ h) A.compF :=
  pullbackRightPullbackFstIso (openBase X g h A) A.P_bar.obj.right.hom
      (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG) ≪≫
    pullback.congrHom (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG) rfl

/-- The forward comparison preserves the projection to Y. -/
theorem firstInteriorIso_hom_toBase :
    (firstInteriorIso X g h A).hom ≫ CompDiagram.toBase X (g ≫ h) A.compF =
      CompDiagram.toBase X g A.compFG := by
  let e := pullbackRightPullbackFstIso (openBase X g h A) A.P_bar.obj.right.hom
    (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)
  let t := pullback.congrHom
    (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)
    (rfl : A.P_bar.obj.right.hom = A.P_bar.obj.right.hom)
  calc
    _ = e.hom ≫ (t.hom ≫ pullback.fst (Of.ι A.P_g) A.P_bar.obj.right.hom) :=
      Category.assoc _ _ _
    _ = e.hom ≫ pullback.fst
        (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG ≫ openBase X g h A)
        A.P_bar.obj.right.hom :=
      congrArg (fun k ↦ e.hom ≫ k) (pullbackCongrHom_first
        (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG) rfl)
    _ = _ := pullbackRightPullbackFstIso_hom_fst
      (openBase X g h A) A.P_bar.obj.right.hom (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)

/-- The reverse comparison also preserves the projection to Y. -/
theorem firstInteriorIso_inv_toBase :
    (firstInteriorIso X g h A).inv ≫ CompDiagram.toBase X g A.compFG =
      CompDiagram.toBase X (g ≫ h) A.compF := by
  rw [Iso.inv_comp_eq]
  exact (firstInteriorIso_hom_toBase X g h A).symm

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram

/-- Equality transport of a pullback cospan preserves its second projection. -/
private theorem pullbackCongrHom_second {C : Type*} [Category C] {P Q R : C}
    {f₁ f₂ : P ⟶ R} {g₁ g₂ : Q ⟶ R} [HasPullback f₁ g₁] [HasPullback f₂ g₂]
    (hf : f₁ = f₂) (hg : g₁ = g₂) :
    (pullback.congrHom hf hg).hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom, pullback.map]

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T]
  (A : AssocDiagram X g h)

/-- The first-interior comparison preserves the actual projection into the common ambient. -/
theorem firstInteriorIso_hom_openImmersion :
    (firstInteriorIso X g h A).hom ≫ CompDiagram.openImmersion X (g ≫ h) A.compF =
      CompDiagram.openImmersion X g A.compFG ≫ openMid X g h A := by
  let e := pullbackRightPullbackFstIso (openBase X g h A) A.P_bar.obj.right.hom
    (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)
  let t := pullback.congrHom
    (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)
    (rfl : A.P_bar.obj.right.hom = A.P_bar.obj.right.hom)
  calc
    _ = e.hom ≫ (t.hom ≫ pullback.snd (Of.ι A.P_g) A.P_bar.obj.right.hom) :=
      Category.assoc _ _ _
    _ = e.hom ≫ pullback.snd
        (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG ≫ openBase X g h A)
        A.P_bar.obj.right.hom :=
      congrArg (fun k ↦ e.hom ≫ k) (pullbackCongrHom_second
        (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG) rfl)
    _ = _ := pullbackRightPullbackFstIso_hom_snd
      (openBase X g h A) A.P_bar.obj.right.hom (CompDiagram.ιInterior (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)

/-- The first-interior comparison preserves the given interior X, and the base Y. -/
theorem firstInteriorIso_hom_interior :
    CompDiagram.ιInterior X g A.compFG ≫ (firstInteriorIso X g h A).hom =
      CompDiagram.ιInterior X (g ≫ h) A.compF := by
  apply (cancel_mono (CompDiagram.openImmersion X (g ≫ h) A.compF)).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ CompDiagram.ιInterior X g A.compFG ≫ k)
      (firstInteriorIso_hom_openImmersion X g h A)).trans
    ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun k ↦ k ≫ openMid X g h A)
      (CompDiagram.ιInterior_comp_openImmersion X g A.compFG)).trans
    ((ιMid_comp_openMid X g h A).trans
      (CompDiagram.ιInterior_comp_openImmersion X (g ≫ h) A.compF).symm))))

/-- The two f-interiors are isomorphic as fixed-interior compactifications over Y. -/
def firstCompactificationIso :
    CompDiagram.ofInterior X g A.compFG ≅ CompDiagram.ofInterior X (g ≫ h) A.compF :=
  ObjectProperty.isoMk _ (Under.isoMk
    (Over.isoMk (firstInteriorIso X g h A) (firstInteriorIso_hom_toBase X g h A))
    (by
      apply CostructuredArrow.hom_ext
      exact firstInteriorIso_hom_interior X g h A))

/-- Its forward ambient arrow is the actual pullback-pasting comparison. -/
theorem firstCompactificationIso_hom_ambient :
    Of.ambientMap (firstCompactificationIso X g h A).hom =
      (firstInteriorIso X g h A).hom := rfl

/-- Its inverse ambient arrow is the actual inverse pullback-pasting comparison. -/
theorem firstCompactificationIso_inv_ambient :
    Of.ambientMap (firstCompactificationIso X g h A).inv =
      (firstInteriorIso X g h A).inv := rfl

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end

/-! The actual pullback-pasting identification between the A and B+C models. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T]
  (A : AssocDiagram X g h)

/-- Pasting the two actual pullbacks identifies the ambient of gammaA with that of gammaBC. -/
def midPastingIso : midInterior X g h A ≅
    CompDiagram.interior (Over.mk (X.hom ≫ g)) h A.compH :=
  pullbackLeftPullbackSndIso (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom

/-- Its forward map is the explicit two-projection lift of the nested pullback. -/
theorem midPastingIso_hom : (midPastingIso X g h A).hom = midPasting X g h A := by
  apply pullback.hom_ext
  · exact (pullbackLeftPullbackSndIso_hom_fst
      (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom).trans
      (midPasting_toBase X g h A).symm
  · exact (pullbackLeftPullbackSndIso_hom_snd
      (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom).trans
      (midPasting_open X g h A).symm

/-- The explicit inverse lift has the prescribed first projection. -/
theorem midPastingInv_first :
    midPastingInv X g h A ≫ toMidBase X g h A = toBaseInterior X g h A :=
  pullback.lift_fst (toBaseInterior X g h A)
    (CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h A.compH) (midPastingInv_fac X g h A)

/-- The explicit inverse lift has the prescribed second projection. -/
theorem midPastingInv_second :
    midPastingInv X g h A ≫ openMid X g h A =
      CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h A.compH :=
  pullback.lift_snd (toBaseInterior X g h A)
    (CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h A.compH) (midPastingInv_fac X g h A)

/-- The inner inverse lift has the prescribed projection to Z. -/
theorem toBaseInterior_first :
    toBaseInterior X g h A ≫ CompDiagram.toBase (Over.mk g) h A.compHG =
      CompDiagram.toBase (Over.mk (X.hom ≫ g)) h A.compH :=
  pullback.lift_fst (CompDiagram.toBase (Over.mk (X.hom ≫ g)) h A.compH)
    (CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h A.compH ≫ A.P_bar.obj.right.hom)
    (toBaseInterior_fac X g h A)

/-- Its inverse is the explicit nested lift, with its specified projections. -/
theorem midPastingIso_inv : (midPastingIso X g h A).inv = midPastingInv X g h A := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · calc
        _ = (midPastingIso X g h A).inv ≫ toMidBase X g h A ≫
            CompDiagram.toBase (Over.mk g) h A.compHG := Category.assoc _ _ _
        _ = CompDiagram.toBase (Over.mk (X.hom ≫ g)) h A.compH :=
          pullbackLeftPullbackSndIso_inv_fst
            (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom
        _ = toBaseInterior X g h A ≫ CompDiagram.toBase (Over.mk g) h A.compHG :=
          (toBaseInterior_first X g h A).symm
        _ = _ := (congrArg (fun k ↦ k ≫ CompDiagram.toBase (Over.mk g) h A.compHG)
          (midPastingInv_first X g h A)).symm
    · calc
        _ = (midPastingIso X g h A).inv ≫ toMidBase X g h A ≫ openBase X g h A :=
          Category.assoc _ _ _
        _ = CompDiagram.openImmersion (Over.mk (X.hom ≫ g)) h A.compH ≫
            A.P_bar.obj.right.hom :=
          pullbackLeftPullbackSndIso_inv_fst_snd
            (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom
        _ = toBaseInterior X g h A ≫ openBase X g h A := (midPastingInv_fac X g h A).symm
        _ = _ := (congrArg (fun k ↦ k ≫ openBase X g h A) (midPastingInv_first X g h A)).symm
  · exact (pullbackLeftPullbackSndIso_inv_snd_snd
      (Of.ι A.P_h) A.P_g.obj.right.hom A.P_bar.obj.right.hom).trans
      (midPastingInv_second X g h A).symm

/-- The forward and inverse lifts are actual inverse morphisms. -/
theorem midPasting_comp_inv : midPasting X g h A ≫ midPastingInv X g h A = 𝟙 _ := by
  rw [← midPastingIso_hom X g h A, ← midPastingIso_inv X g h A]
  exact (midPastingIso X g h A).hom_inv_id

/-- The reverse composite is also the identity. -/
theorem midPasting_inv_comp : midPastingInv X g h A ≫ midPasting X g h A = 𝟙 _ := by
  rw [← midPastingIso_hom X g h A, ← midPastingIso_inv X g h A]
  exact (midPastingIso X g h A).inv_hom_id

/-- The actual A-composite and B+C-interior compactifications are canonically isomorphic. -/
def ofCompositeFG_iso_ofInteriorH :
    CompDiagram.ofComposite X g A.compFG ≅
      CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH where
  hom := ofCompositeFG_hom_ofInteriorH X g h A
  inv := ofInteriorH_hom_ofCompositeFG X g h A
  hom_inv_id := by
    apply InducedCategory.hom_ext
    apply StructuredArrow.hom_ext
    apply CostructuredArrow.hom_ext
    change (𝟙 _ ≫ midPasting X g h A ≫ 𝟙 _) ≫
      (𝟙 _ ≫ midPastingInv X g h A ≫ 𝟙 _) = 𝟙 _
    simpa only [Category.id_comp, Category.comp_id] using midPasting_comp_inv X g h A
  inv_hom_id := by
    apply InducedCategory.hom_ext
    apply StructuredArrow.hom_ext
    apply CostructuredArrow.hom_ext
    change (𝟙 _ ≫ midPastingInv X g h A ≫ 𝟙 _) ≫
      (𝟙 _ ≫ midPasting X g h A ≫ 𝟙 _) = 𝟙 _
    simpa only [Category.id_comp, Category.comp_id] using midPasting_inv_comp X g h A

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end

/-! Concrete geometric bridges for the distinct A+B and B+C codomains. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T]
  (A : AssocDiagram X g h)

/-- The A+B ambient map is the right-associated composite of the three proper maps. -/
theorem compositeAB_map :
    (CompDiagram.ofComposite X (g ≫ h) A.compF).obj.right.hom =
      A.P_bar.obj.right.hom ≫ (A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom) := rfl

/-- The B+C ambient map is the left-associated composite of the same proper maps. -/
theorem compositeBC_map :
    (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH).obj.right.hom =
      (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom) ≫ A.P_h.obj.right.hom := rfl

/-- The geometric codomain comparison follows from actual category associativity. -/
theorem compositeBC_map_eq_AB :
    (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH).obj.right.hom =
      (CompDiagram.ofComposite X (g ≫ h) A.compF).obj.right.hom :=
  Category.assoc A.P_bar.obj.right.hom A.P_g.obj.right.hom A.P_h.obj.right.hom

/-- The two ambient schemes over T are identified by the identity on the common ambient. -/
def compositeAmbientIso :
    (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH).obj.right ≅
      (CompDiagram.ofComposite X (g ≫ h) A.compF).obj.right :=
  (Over.isoMk (Iso.refl A.P_bar.obj.right.left)
    ((Category.id_comp (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom)).trans
      (Category.assoc A.P_bar.obj.right.hom A.P_g.obj.right.hom A.P_h.obj.right.hom).symm) :
    Over.mk ((A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom) ≫ A.P_h.obj.right.hom) ≅
      Over.mk (A.P_bar.obj.right.hom ≫ A.P_g.obj.right.hom ≫ A.P_h.obj.right.hom))

/-- The forward ambient map is literally the identity, on the common ambient. -/
theorem compositeAmbientIso_hom_left : (compositeAmbientIso X g h A).hom.left = 𝟙 _ := rfl

/-- The reverse ambient map is also literally the identity. -/
theorem compositeAmbientIso_inv_left : (compositeAmbientIso X g h A).inv.left = 𝟙 _ := rfl

/-- The A+B interior composition is exactly the given P_bar interior. -/
theorem compositeAB_interior :
    Of.ι (CompDiagram.ofComposite X (g ≫ h) A.compF) = Of.ι A.P_bar :=
  CompDiagram.ιInterior_comp_openImmersion X (g ≫ h) A.compF

/-- The B+C interior composition is exactly the same P_bar interior. -/
theorem compositeBC_interior :
    Of.ι (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH) = Of.ι A.P_bar :=
  CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T]
  (A : AssocDiagram X g h)

/-- The C-composite and A+B base are the same geometric compactification via identity on the ambient. -/
def baseCompactificationIso :
    CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG ≅ A.compF.P_g :=
  ObjectProperty.isoMk _ (Under.isoMk
    (Over.isoMk (Iso.refl A.P_g.obj.right.left) (Category.id_comp _))
    (by
      apply CostructuredArrow.hom_ext
      exact (Category.comp_id _).trans
        (CompDiagram.ιInterior_comp_openImmersion (h_f_separated := inferInstanceAs (IsSeparated g))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType g))
      (h_X_compact := inferInstanceAs (CompactSpace Y))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h A.compHG)))

/-- The forward geometric base transition is the identity on the ambient of g. -/
theorem baseCompactificationIso_hom_ambient :
    Of.ambientMap (baseCompactificationIso X g h A).hom = 𝟙 A.P_g.obj.right.left := rfl

/-- The reverse geometric base transition is also the literal identity. -/
theorem baseCompactificationIso_inv_ambient :
    Of.ambientMap (baseCompactificationIso X g h A).inv = 𝟙 A.P_g.obj.right.left := rfl

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end

@[expose] public section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T] (A : AssocDiagram X g h)

/-- The actual A+B compactification, with right-associated structure map. -/
abbrev finalAB := CompDiagram.ofComposite X (g ≫ h) A.compF

/-- The actual B+C compactification, with left-associated structure map. -/
abbrev finalBC := CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
      (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType (X.hom ≫ g)))
      (h_X_compact := inferInstanceAs (CompactSpace X.left))
      (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left)) (Over.mk (X.hom ≫ g)) h A.compH

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.AssocDiagram
end

@[expose] public section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification
noncomputable section
universe u v

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.CanonicalAssociativity

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T] (A : AssocDiagram X g h)

/-- The A+B ambient over the left-associated composite, using its actual triangle. -/
def endpointAB :
    Of T (Over.mk ((X.hom ≫ g) ≫ h)) :=
  let j : Over.mk ((X.hom ≫ g) ≫ h) ⟶ (AssocDiagram.finalAB X g h A).obj.right :=
    Over.homMk (Of.ι (AssocDiagram.finalAB X g h A))
      ((Over.w (AssocDiagram.finalAB X g h A).obj.hom).trans
        (Category.assoc X.hom g h).symm)
  @Of.mk T (Over.mk ((X.hom ≫ g) ≫ h))
    (AssocDiagram.finalAB X g h A).obj.right j
    (Of.instIsOpenImmersion T (Over.mk (X.hom ≫ (g ≫ h)))
      (AssocDiagram.finalAB X g h A))
    (AssocDiagram.finalAB X g h A).property.quasiCompact
    (AssocDiagram.finalAB X g h A).property.isProper

/-- Identity on the common ambient, with the actual endpoint triangle equalities. -/
def endpointIso :
    AssocDiagram.finalBC X g h A ≅ endpointAB X g h A :=
  ObjectProperty.isoMk _ (Under.isoMk
    (AssocDiagram.compositeAmbientIso X g h A)
    (by
      apply CostructuredArrow.hom_ext
      exact (Category.comp_id _).trans
        ((AssocDiagram.compositeBC_interior X g h A).trans
          (AssocDiagram.compositeAB_interior X g h A).symm)))

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.CanonicalAssociativity
end
