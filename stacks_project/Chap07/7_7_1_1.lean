module

public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Equalizer.Presieve.Arrows

universe t w v u

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type w)
variable {B : C} {I : Type t} [Small.{w} I] (X : I → C) (π : (i : I) → X i ⟶ B)
variable [(Presieve.ofArrows X π).HasPairwisePullbacks]

/- 7.7.1.1: the sheaf-condition diagram
   P.obj (op B) ⟶ FirstObj P X ⇉ SecondObj P X π,
   i.e. F(U) ⟶ ∏ᶜ fun i ↦ P.obj (op (X i)) ⇉
   ∏ᶜ fun ij : I × I ↦ P.obj (op (pullback (π ij.1) (π ij.2))),
   with parallel maps firstMap = pr₀* and secondMap = pr₁*. -/
@[stacks 00VN] #check (forkMap P X π : P.obj (op B) ⟶ FirstObj P X)

#check (firstMap P X π : FirstObj P X ⟶ SecondObj P X π)
#check (secondMap P X π : FirstObj P X ⟶ SecondObj P X π)
#check (FirstObj P X : Type w)
#check (SecondObj P X π : Type w)
#check Fork.ofι (forkMap P X π) (w P X π)
