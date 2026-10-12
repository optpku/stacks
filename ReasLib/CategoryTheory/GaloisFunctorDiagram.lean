/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.Galois.Action
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.ObjectProperty.FiniteCoproductClosure

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

universe uC vC uC' vC' uC'' vC'' w

namespace CategoryTheory

/-- A chain of two 2-commutative squares induced by exact functors of Galois categories. -/
structure GaloisFunctorDiagram
    {C : Type uC} [Category.{vC} C] [GaloisCategory C]
    {C' : Type uC'} [Category.{vC'} C'] [GaloisCategory C']
    {C'' : Type uC''} [Category.{vC''} C''] [GaloisCategory C'']
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']
    (F'' : C'' ⥤ FintypeCat.{w}) [FiberFunctor F''] where
  /-- The first exact functor in the displayed chain. -/
  H : C ⥤ C'
  /-- The second exact functor in the displayed chain. -/
  H' : C' ⥤ C''
  /-- The continuous homomorphism from `Aut F'` to `Aut F`. -/
  h : ContinuousMonoidHom (Aut F') (Aut F)
  /-- The continuous homomorphism from `Aut F''` to `Aut F'`. -/
  h' : ContinuousMonoidHom (Aut F'') (Aut F')
  /-- Exactness of the first functor. -/
  exactLeft : exactFunctor C C' H
  /-- Exactness of the second functor. -/
  exactRight : exactFunctor C' C'' H'
  /-- The left 2-commutative square of the displayed chain. -/
  leftSquare :
    CatCommSq H (functorToAction F) (functorToAction F')
      (Action.res FintypeCat h.toMonoidHom)
  /-- The right 2-commutative square of the displayed chain. -/
  rightSquare :
    CatCommSq H' (functorToAction F') (functorToAction F'')
      (Action.res FintypeCat h'.toMonoidHom)

/-- Construct a `GaloisFunctorDiagram` from its functors, homomorphisms, and square data. -/
def GaloisFunctorDiagram.of
    {C : Type uC} [Category.{vC} C] [GaloisCategory C]
    {C' : Type uC'} [Category.{vC'} C'] [GaloisCategory C']
    {C'' : Type uC''} [Category.{vC''} C''] [GaloisCategory C'']
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']
    (F'' : C'' ⥤ FintypeCat.{w}) [FiberFunctor F'']
    (H : C ⥤ C') (H' : C' ⥤ C'')
    (h : ContinuousMonoidHom (Aut F') (Aut F))
    (h' : ContinuousMonoidHom (Aut F'') (Aut F'))
    (exactLeft : exactFunctor C C' H)
    (exactRight : exactFunctor C' C'' H')
    (leftSquare :
      CatCommSq H (functorToAction F) (functorToAction F')
        (Action.res FintypeCat h.toMonoidHom))
    (rightSquare :
      CatCommSq H' (functorToAction F') (functorToAction F'')
        (Action.res FintypeCat h'.toMonoidHom)) :
    GaloisFunctorDiagram F F' F'' :=
  { H := H
    H' := H'
    h := h
    h' := h'
    exactLeft := exactLeft
    exactRight := exactRight
    leftSquare := leftSquare
    rightSquare := rightSquare }

/-- Return the left and right squares of a `GaloisFunctorDiagram` in display order. -/
def GaloisFunctorDiagram.toSquares
    {C : Type uC} [Category.{vC} C] [GaloisCategory C]
    {C' : Type uC'} [Category.{vC'} C'] [GaloisCategory C']
    {C'' : Type uC''} [Category.{vC''} C''] [GaloisCategory C'']
    {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
    {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']
    {F'' : C'' ⥤ FintypeCat.{w}} [FiberFunctor F'']
    (D : GaloisFunctorDiagram F F' F'') :
    CatCommSq D.H (functorToAction F) (functorToAction F')
      (Action.res FintypeCat D.h.toMonoidHom) ×
    CatCommSq D.H' (functorToAction F') (functorToAction F'')
      (Action.res FintypeCat D.h'.toMonoidHom) :=
  (D.leftSquare, D.rightSquare)

end CategoryTheory

namespace CategoryTheory.GaloisFunctorDiagram

/-- The image under the first functor of the chosen terminal object is terminal. -/
noncomputable def isTerminal_obj_top
    {C : Type uC} [Category.{vC} C] [GaloisCategory C]
    {C' : Type uC'} [Category.{vC'} C'] [GaloisCategory C']
    {C'' : Type uC''} [Category.{vC''} C''] [GaloisCategory C'']
    {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
    {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']
    {F'' : C'' ⥤ FintypeCat.{w}} [FiberFunctor F'']
    (D : GaloisFunctorDiagram F F' F'') : IsTerminal (D.H.obj (⊤_ C)) := by
  -- Local instance justification (proof-local temporary data): Expose the finite-limit preservation component of the explicit diagram's exactness solely to construct its terminal comparison.
  letI : PreservesFiniteLimits D.H := D.exactLeft.1
  exact isLimitOfHasTerminalOfPreservesLimit D.H

/-- The composite homomorphism is trivial exactly when the composite functor
has image in the finite-coproduct closure of terminal objects. -/
theorem comp_trivial_iff
    {C : Type uC} [Category.{vC} C] [GaloisCategory C]
    {C' : Type uC'} [Category.{vC'} C'] [GaloisCategory C']
    {C'' : Type uC''} [Category.{vC''} C''] [GaloisCategory C'']
    {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
    {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']
    {F'' : C'' ⥤ FintypeCat.{w}} [FiberFunctor F'']
    (D : GaloisFunctorDiagram F F' F'') :
    D.h.comp D.h' = 1 ↔
      (⊤ : ObjectProperty C).map (D.H ⋙ D.H') ≤
        ObjectProperty.additiveClosure (fun X : C'' ↦ Nonempty (IsTerminal X)) := sorry

/-- The five standard characterizations of surjectivity for the first map in a Galois functor diagram are equivalent. -/
theorem tfae
    {C : Type uC} [Category.{vC} C] [GaloisCategory C]
    {C' : Type uC'} [Category.{vC'} C'] [GaloisCategory C']
    {C'' : Type uC''} [Category.{vC''} C''] [GaloisCategory C'']
    {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
    {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']
    {F'' : C'' ⥤ FintypeCat.{w}} [FiberFunctor F'']
    (D : GaloisFunctorDiagram F F' F'') :
    List.TFAE [
      Function.Surjective D.h,
      Nonempty D.H.FullyFaithful,
      PreservesIsConnected D.H,
      ∀ X : C, PreGaloisCategory.IsConnected X → Nonempty (⊤_ C' ⟶ D.H.obj X) →
        Nonempty (⊤_ C ⟶ X),
      ∀ X : C, Function.Bijective (fun f : (⊤_ C ⟶ X) ↦
        (isTerminal_obj_top D).from (⊤_ C') ≫ D.H.map f)] := sorry

/-- Exactness of the induced automorphism-group sequence is equivalent to the
essential-image and epimorphic-cover characterizations of the second functor. -/
theorem exactSequence_tfae
    {C : Type uC} [Category.{vC} C] [GaloisCategory C]
    {C' : Type uC'} [Category.{vC'} C'] [GaloisCategory C']
    {C'' : Type uC''} [Category.{vC''} C''] [GaloisCategory C'']
    {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
    {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']
    {F'' : C'' ⥤ FintypeCat.{w}} [FiberFunctor F'']
    (D : GaloisFunctorDiagram F F' F'') :
    List.TFAE [
      Function.Surjective D.h ∧
        D.h.comp D.h' = 1 ∧
        MonoidHom.ker D.h.toMonoidHom =
          (Subgroup.normalClosure
            (MonoidHom.range D.h'.toMonoidHom : Set (Aut F'))).topologicalClosure,
      Nonempty D.H.FullyFaithful ∧
        D.H.essImage =
          (ObjectProperty.additiveClosure
            (fun X : C'' ↦ Nonempty (IsTerminal X))).inverseImage D.H',
      Nonempty D.H.FullyFaithful ∧
        (⊤ : ObjectProperty C).map (D.H ⋙ D.H') ≤
          ObjectProperty.additiveClosure
            (fun X : C'' ↦ Nonempty (IsTerminal X)) ∧
        ∀ X' : C',
          ObjectProperty.additiveClosure
              (fun X : C'' ↦ Nonempty (IsTerminal X)) (D.H'.obj X') →
            ∃ (X : C) (f : D.H.obj X ⟶ X'), Epi f] := sorry

/-- The second homomorphism is injective exactly when every connected object in the
second Galois category admits an epimorphic cover embedding into the image of the
second functor. -/
theorem h'_injective_iff
    {C : Type uC} [Category.{vC} C] [GaloisCategory C]
    {C' : Type uC'} [Category.{vC'} C'] [GaloisCategory C']
    {C'' : Type uC''} [Category.{vC''} C''] [GaloisCategory C'']
    {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
    {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']
    {F'' : C'' ⥤ FintypeCat.{w}} [FiberFunctor F'']
    (D : GaloisFunctorDiagram F F' F'') :
    Function.Injective D.h' ↔
      ∀ (X'' : C'') [PreGaloisCategory.IsConnected X''],
        ∃ (X' : C') (Y'' : C'') (p : Y'' ⟶ X'')
          (q : Y'' ⟶ D.H'.obj X'), Epi p ∧ Mono q := sorry

/-- The image of the second homomorphism is normal exactly when every connected
object of the middle Galois category receiving a map from the terminal object
of the third category is a finite coproduct of terminal objects. -/
theorem normalRange_iff_finiteCoproductTerminal
    {C : Type uC} [Category.{vC} C] [GaloisCategory C]
    {C' : Type uC'} [Category.{vC'} C'] [GaloisCategory C']
    {C'' : Type uC''} [Category.{vC''} C''] [GaloisCategory C'']
    {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
    {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']
    {F'' : C'' ⥤ FintypeCat.{w}} [FiberFunctor F'']
    (D : GaloisFunctorDiagram F F' F'') :
    Subgroup.Normal (MonoidHom.range D.h'.toMonoidHom) ↔
      ∀ (X' : C') [PreGaloisCategory.IsConnected X'],
        Nonempty ((⊤_ C'') ⟶ D.H'.obj X') →
          ∃ n : ℕ, ∃ Y : Fin n → C'',
            (∀ i, Nonempty (IsTerminal (Y i))) ∧
              Nonempty ((∐ Y) ≅ D.H'.obj X') := sorry

end CategoryTheory.GaloisFunctorDiagram
