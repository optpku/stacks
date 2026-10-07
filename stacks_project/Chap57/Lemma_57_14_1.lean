module

public import stacks_project.Chap57.Lemma_57_14_1_Category

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Lemma 57.14.1: base change along `g : S' ⟶ S` sends the Fourier--Mukai kernel category of
smooth proper schemes over `S` to the corresponding category over `S'`.  Its object map is the
canonical pullback `S' ×_S X`, and its morphism map is derived pullback on perfect-kernel
isomorphism classes along the induced product comparison morphism. -/
@[stacks 0G0G]
noncomputable def fourierMukaiKernelBaseChange
    {S S' : Scheme.{u}} (g : S' ⟶ S) :
    FourierMukaiObject S ⥤ FourierMukaiObject S' where
  obj := FourierMukaiObject.baseChange g
  map := fun {X Y} f ↦ FourierMukaiObject.mapKernel g X Y f
  map_id := FourierMukaiObject.mapKernel_id g
  map_comp := FourierMukaiObject.mapKernel_comp g

/-- The base-change functor acts on objects by the canonical pullback construction. -/
@[stacks 0G0G]
theorem fourierMukaiKernelBaseChange_obj
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    (X : FourierMukaiObject S) :
    (fourierMukaiKernelBaseChange g).obj X =
      FourierMukaiObject.baseChange g X := sorry
