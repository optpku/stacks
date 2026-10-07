module

public import stacks_project.Chap81.Lemma_81_6_6_Flat
public import stacks_project.Chap81.Lemma_81_6_6_Pushout
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits SheafOfModules

universe u

/- Lemma 81.6.6 (1): pullback from `V'` identifies relatively flat quasi-coherent modules
with compatible relatively flat quasi-coherent modules on `V` and `U'`. -/
@[stacks 08KV] #check
  (AlgebraicGeometry.AlgebraicSpace.FlatQCoh.Pushout.gluingFunctorIsEquivalence :
    ∀ {S : Scheme.{u}} {X X' Y V' : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f] (p : V' ⟶ pushout i f),
      Functor.IsEquivalence
        (AlgebraicGeometry.AlgebraicSpace.FlatQCoh.Pushout.gluingFunctor i f p))

/- Lemma 81.6.6 (2): a relatively flat quasi-coherent module on `V'` is of finite type if
and only if both components of its canonical gluing datum are of finite type. -/
@[stacks 08KV] #check
  (AlgebraicGeometry.AlgebraicSpace.FlatQCoh.Pushout.finiteType_iff :
    ∀ {S : Scheme.{u}} {X X' Y V' : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f] (p : V' ⟶ pushout i f)
      (G' : AlgebraicGeometry.AlgebraicSpace.FlatQCoh p),
      IsFiniteType G'.obj.obj ↔
        IsFiniteType
            ((AlgebraicGeometry.AlgebraicSpace.FlatQCoh.Pushout.gluingFunctor i f p).obj
                G').fst.obj.obj ∧
          IsFiniteType
            ((AlgebraicGeometry.AlgebraicSpace.FlatQCoh.Pushout.gluingFunctor i f p).obj
                G').snd.obj.obj)

/- Lemma 81.6.6 (3): when `p` is locally of finite presentation, a relatively flat
quasi-coherent module on `V'` is finitely presented if and only if both components of its
canonical gluing datum are finitely presented. -/
@[stacks 08KV] #check
  (AlgebraicGeometry.AlgebraicSpace.FlatQCoh.Pushout.finitePresentation_iff :
    ∀ {S : Scheme.{u}} {X X' Y V' : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f] (p : V' ⟶ pushout i f)
      [LocallyOfFinitePresentation p] (G' : AlgebraicGeometry.AlgebraicSpace.FlatQCoh p),
      IsFinitePresentation G'.obj.obj ↔
        IsFinitePresentation
            ((AlgebraicGeometry.AlgebraicSpace.FlatQCoh.Pushout.gluingFunctor i f p).obj
                G').fst.obj.obj ∧
          IsFinitePresentation
            ((AlgebraicGeometry.AlgebraicSpace.FlatQCoh.Pushout.gluingFunctor i f p).obj
                G').snd.obj.obj)
