module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Subobject
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of module-sheaf subobjects

This file owns the submodule of a stalk obtained as the range of a subobject inclusion.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.Subobject

variable {Z : TopCat.{u}} {𝒪 : Z.Sheaf RingCat.{u}}
variable {ℱ : SheafOfModules 𝒪}

/-- The image in the stalk at `x` of a module-sheaf subobject. -/
@[stacks 01AR "subobject stalk range"]
noncomputable def stalkRange (G : CategoryTheory.Subobject ℱ) (x : Z) :
    Submodule (𝒪.presheaf.stalk x) ((stalkFunctor 𝒪 x).obj ℱ) :=
  ((stalkFunctor 𝒪 x).map G.arrow).hom.range

/-- Membership in a subobject stalk range is witnessed by an element of the subobject stalk. -/
theorem mem_stalkRange
    (G : CategoryTheory.Subobject ℱ) (x : Z) (m : (stalkFunctor 𝒪 x).obj ℱ) :
    m ∈ stalkRange G x ↔
      ∃ t : (stalkFunctor 𝒪 x).obj (G : SheafOfModules 𝒪),
        ((stalkFunctor 𝒪 x).map G.arrow).hom t = m := sorry

namespace CommRing

variable {𝒪 : Z.Sheaf CommRingCat.{u}}
variable {ℱ : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)}

/-- The image in the commutative-ring stalk at `x` of a module-sheaf subobject. -/
@[stacks 01AR "commutative subobject stalk range"]
noncomputable def stalkRange (G : CategoryTheory.Subobject ℱ) (x : Z) :
    Submodule (𝒪.presheaf.stalk x) ((stalkFunctorOfCommRing 𝒪 x).obj ℱ) :=
  ((stalkFunctorOfCommRing 𝒪 x).map G.arrow).hom.range

/-- Membership in a commutative subobject stalk range is witnessed by an element of the
subobject stalk. -/
theorem mem_stalkRange
    (G : CategoryTheory.Subobject ℱ) (x : Z)
    (m : (stalkFunctorOfCommRing 𝒪 x).obj ℱ) :
    m ∈ stalkRange G x ↔
      ∃ t : (stalkFunctorOfCommRing 𝒪 x).obj
          (G : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)),
        ((stalkFunctorOfCommRing 𝒪 x).map G.arrow).hom t = m := sorry

end CommRing

end SheafOfModules.Subobject
