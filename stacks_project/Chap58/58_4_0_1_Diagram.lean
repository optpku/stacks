module

public import ReasLib.CategoryTheory.GaloisFunctorDiagram

universe uC vC uC' vC' uC'' vC'' w

open CategoryTheory
open CategoryTheory.PreGaloisCategory

/- Public compatibility check for the promoted Galois-category diagram. -/
#check (CategoryTheory.GaloisFunctorDiagram :
  {C : Type uC} → [Category.{vC} C] → [GaloisCategory C] →
  {C' : Type uC'} → [Category.{vC'} C'] → [GaloisCategory C'] →
  {C'' : Type uC''} → [Category.{vC''} C''] → [GaloisCategory C''] →
  (F : C ⥤ FintypeCat.{w}) → [FiberFunctor F] →
  (F' : C' ⥤ FintypeCat.{w}) → [FiberFunctor F'] →
  (F'' : C'' ⥤ FintypeCat.{w}) → [FiberFunctor F''] → Type _)
