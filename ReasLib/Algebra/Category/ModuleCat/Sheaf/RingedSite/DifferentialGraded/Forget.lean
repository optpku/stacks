/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.GradedModule
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module

/-!
# Forgetting the differential

This leaf owns the functor from differential graded modules to graded modules in the matching
tensor-morphism presentation, together with its degreewise computation API.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

namespace DifferentialGradedModule

/-- Forget the differential of a differential graded module and retain its graded action. -/
def forgetToGraded (𝒜 : DGA(𝒪)) :
    Mod(𝒜, d) ⥤ DifferentialGradedAlgebra.GradedModule 𝒜 where
  obj M :=
    { obj := M.toComplex.X
      smul := M.smul
      smul_assoc := M.smul_assoc
      one_smul := M.one_smul }
  map f :=
    { hom := f.toCochainMap.f
      comm := f.comm }
  map_id := sorry
  map_comp := sorry

/-- Forgetting the differential preserves the object in each degree. -/
@[simp]
theorem forgetToGraded_obj_obj (𝒜 : DGA(𝒪)) (M : Mod(𝒜, d)) (n : ℤ) :
    ((forgetToGraded 𝒜).obj M).obj n = M.toComplex.X n := sorry

/-- Forgetting a morphism preserves its map in each degree. -/
@[simp]
theorem forgetToGraded_map_hom
    (𝒜 : DGA(𝒪)) {M N : Mod(𝒜, d)} (f : M ⟶ N) (n : ℤ) :
    ((forgetToGraded 𝒜).map f).hom n = f.toCochainMap.f n := sorry

/-- The forgetful functor from differential graded modules to graded modules is faithful. -/
instance forgetToGraded_faithful (𝒜 : DGA(𝒪)) :
    Functor.Faithful (forgetToGraded 𝒜) where
  map_injective := sorry

end DifferentialGradedModule

end


end SheafOfModules.RingedSite
