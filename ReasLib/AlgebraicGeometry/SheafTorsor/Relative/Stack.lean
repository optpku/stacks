module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import ReasLib.AlgebraicGeometry.SheafTorsor.Relative.Category
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic

/-!
# The stack of relative sheaf torsors

Relative torsors under a group object over an fppf sheaf form a stack in groupoids
with essentially small fibers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SheafTorsorsOver

variable {S : Scheme.{u}} {ℬ : Sheaf (Scheme.fppfTopology.over S) (Type u)}

/-- The relative torsor projection is a stack in groupoids on the fppf site. -/
instance isStackInGroupoids (𝒢 : Grp (Over ℬ)) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget 𝒢) := sorry

/-- The stack in groupoids of `𝒢/ℬ-torsors` over `(Sch/S)_fppf`. -/
def stack (𝒢 : Grp (Over ℬ)) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (forget 𝒢)

/-- The projection of `stack` is the forgetful functor to `(Sch/S)_fppf`. -/
theorem stack_p (𝒢 : Grp (Over ℬ)) : (stack 𝒢).p = forget 𝒢 := rfl

/-- Each fiber of the relative torsor projection has a set of isomorphism class
representatives in the universe of group sections. -/
instance fibers_essentiallySmall (𝒢 : Grp (Over ℬ)) (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((forget 𝒢).Fiber U)) := sorry

/-- The relative torsor projection is a stack in groupoids with essentially small fibers. -/
theorem isStackWithSmallFibers (𝒢 : Grp (Over ℬ)) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (forget 𝒢) ∧
      ∀ U : Over S, ObjectProperty.EssentiallySmall.{u}
        (⊤ : ObjectProperty ((forget 𝒢).Fiber U)) :=
  ⟨isStackInGroupoids 𝒢, fibers_essentiallySmall 𝒢⟩

end AlgebraicGeometry.SheafTorsorsOver
