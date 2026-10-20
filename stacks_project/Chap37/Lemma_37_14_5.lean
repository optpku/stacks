/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Pushout
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules
open scoped AlgebraicGeometry

universe u

/- Lemma 37.14.5 (1): pullback from `V'` identifies relatively flat quasi-coherent modules
with compatible relatively flat quasi-coherent modules on `V` and `U'`. -/
@[stacks 08KU] #check
  (AlgebraicGeometry.Scheme.FlatQCoh.Pushout.gluingFunctorIsEquivalence :
    ∀ {X X' Y V' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f] (p : V' ⟶ pushout i f),
      Functor.IsEquivalence
        (AlgebraicGeometry.Scheme.FlatQCoh.Pushout.gluingFunctor i f p))

/- Lemma 37.14.5 (2): a relatively flat quasi-coherent module on `V'` is of finite type if
and only if both components of its canonical gluing datum are of finite type. -/
@[stacks 08KU] #check
  (AlgebraicGeometry.Scheme.FlatQCoh.Pushout.finiteType_iff :
    ∀ {X X' Y V' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f] (p : V' ⟶ pushout i f)
      (G' : AlgebraicGeometry.Scheme.FlatQCoh p),
      IsFiniteType G'.obj.obj ↔
        IsFiniteType
            ((AlgebraicGeometry.Scheme.FlatQCoh.Pushout.gluingFunctor i f p).obj G').fst.obj.obj ∧
          IsFiniteType
            ((AlgebraicGeometry.Scheme.FlatQCoh.Pushout.gluingFunctor i f p).obj G').snd.obj.obj)

/- Lemma 37.14.5 (3): when `p` is locally of finite presentation, a relatively flat
quasi-coherent module on `V'` is finitely presented if and only if both components of its
canonical gluing datum are finitely presented. -/
@[stacks 08KU] #check
  (AlgebraicGeometry.Scheme.FlatQCoh.Pushout.finitePresentation_iff :
    ∀ {X X' Y V' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [IsAffineHom f] (p : V' ⟶ pushout i f)
      [LocallyOfFinitePresentation p] (G' : AlgebraicGeometry.Scheme.FlatQCoh p),
      IsFinitePresentation G'.obj.obj ↔
        IsFinitePresentation
            ((AlgebraicGeometry.Scheme.FlatQCoh.Pushout.gluingFunctor i f p).obj G').fst.obj.obj ∧
          IsFinitePresentation
            ((AlgebraicGeometry.Scheme.FlatQCoh.Pushout.gluingFunctor i f p).obj G').snd.obj.obj)
