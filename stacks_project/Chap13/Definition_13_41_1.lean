module

import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory

-- Definition 13.41.1: finite Postnikov systems and their morphisms are owned by the reusable
-- pretriangulated API over `ComposableArrows`.
@[stacks 0D7Z] #check @CategoryTheory.PostnikovSystem
#check @CategoryTheory.PostnikovSystem.Morphism

-- The reusable morphism API exposes stage triangles without requiring downstream users to
-- unfold the compatibility-square fields.
@[stacks 0D7Z] #check @CategoryTheory.PostnikovSystem.Morphism.triangleMorphism
@[stacks 0D7Z] #check @CategoryTheory.PostnikovSystem.Morphism.triangleMorphism.hom₁
@[stacks 0D7Z] #check @CategoryTheory.PostnikovSystem.Morphism.triangleMorphism.hom₂
@[stacks 0D7Z] #check @CategoryTheory.PostnikovSystem.Morphism.triangleMorphism.hom₃
@[stacks 0D7Z] #check @CategoryTheory.PostnikovSystem.Morphism.triangleMorphism.id
@[stacks 0D7Z] #check @CategoryTheory.PostnikovSystem.Morphism.triangleMorphism.comp
@[stacks 0D7Z] #check @CategoryTheory.PostnikovSystem.Morphism.tail_yMap
